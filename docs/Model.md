# The Pure Shake Model

Shake takes as primitive a notion of correctness based on a mapping from input dictionaries to resultant dictionaries. Conceptually, the world may be represented as a key-value dictionary (for example, a physics approach would map (particle name, time) to position and other state), so this is quite generic. In particular Shake assumes that correctness follows "the Shake model", a Haskell library loosely similar to imperative-style Shake programs.

First, we have dictionaries, which we'll represent as functions for ease of use:
    type Dictionary = Key -> Value
Rules are functions on dictionaries:
    type Rule = Dictionary -> Dictionary
Need and apply translate as function application:
    apply [a "x"] --> \d k -> a "x" d k
For parallel application, we require that each changed key is changed only once:
    need [a,b] --> \d k -> case filter (/= d k) . map (\x -> x d k) $ [a,b] of
        [] -> d k
        [a] -> a
        _ -> undefined
A similar consideration applies to combining the environment of 'parallel'. A looser variation might allow confluent writes, but we don't.
External commands as well as liftIO etc. translate as pure Haskell functions:
    cmd $ "gcc a.c -o a.o" --> \d k -> if k == "a.o" then gcc (d "a.c") else d k
Finally, monadic computation translates as composition (Haskell values are erased; if they are relevant they can be stored in the dictionary):
    a >> b --> \d k -> let d' = a d in b d' k
Default rules for source files translate as identity:
    need [source_file] = id

# Hermetic Builds

The pure model alone does not constitute Shake, as Shake does not actually use a pure `Key -> Value` dictionary type. One can think of Shake as a library providing the pure model on top of an impure world. Most results are stored directly on the filesystem or in Shake's internal database.

To implement this, Shake requires that rules either declare their inputs, outputs, and dependencies, or run in a tracing mode which computes this information. Shake also support a "tracing lint mode", which traces the declared operations and verifies that they match. The tracing system is incomplete at present; for example, it does not record absent files. We could imagine a tracer that fixed these shortcomings; a "super-tracer". If, for all builds of a build system, the declared or traced dependencies match those of the super-tracer, then the build system is said to be hermetic; that is, each rule uses only its declared inputs and dependencies and writes only its declared outputs.

Shake guarantees the correctness of hermetic build systems; any series of builds (clean, incremental, partial, even those interrupted in the middle) ending with a successful full build, starting from the same input, will result in output identical to the pure model version of the build system. Shake also guarantees that running 'shake clean' will restore the state of the world to the initial input.

# Consistent Rebuilds

Consider an action such as
    do
      (n :: Int) <- read <$> readFile "a"
      writeFile "a" (show $ n + 1)

By the semantics of the pure model, the two values must be stored separately. the good news is this only applies to initial vs generated files;

we should never see n+2. Choices:
- (redirected reads): we can copy the initial file elsewhere, then change the read call to read from that file
- (redirected writes): we can preserve the initial file on-disk, and change the write to store it elsewhere
- (error): we can detect this situation and disallow it, forcing users to do one of the above

Erroring seems like the most flexible option, since the user can pick which file to redirect. OTOH, sometimes cyclic feedback is actually desired, e.g. when command-line options change a config file for all future runs - solved by having sticky rules.

Also, generated files will overwrite their target unconditionally.

# Incremental changes

This picture of the world assumes that the input dictionary is static. It is not. So, let us start by introducing


Fortunately, we do not have to think about this; incrementalization is an automated type-directed process. In ML, there's some complexity due to mutable references, but in Haskell, due to laziness, we can use monads and it's pretty easy. Unsurprisingly, we cannot use the Adaptive library as-is; it uses an ordered list implementation, while what we really need is a graph-based algorithm.

Files are just modifiables.



We store incoming edges in a weak hash table, relying on OCaml’s garbage collector to remove irrelevant edges. If an edge is clean, then all edges transitively reachable by outgoing edges beginning from the target thunk will also be clean, which amortizes change propagation cost across consecutive calls to force.

Order Maintenance Set (Time Stamps): constant time operations: insert new after, delete, compare
Searchable Time-Ordered Sets (TimeMap): set from [(t,v)], t is unique. plus logarithmic operations: insert at t, delete at t, find earliest after t, find latest before t

global time line
global priority queue containing the affected readers prioritized by their start time (we define readers more precisely below)
timestamps: current time, end-of-memo
during the initial run, the current-time is always the last time stamp, but during change propagation it can be any time in the past
During evaluation and change propagation, we advance the time by inserting a new time stamp t immediately after current-time and setting the current time to t

modifiable (TimeMap of versioned values, TimeMap of read operations (start t, end t, read function), equality)
  new = (empty, empty, equal operation)
  read :: Mod -> f -> ()
  read (vs,rs,_) f= do
    t <- current-time
    (time, v) <- latest value before current-time of vs
    ts <- incCurrentTime
    () <- f v
    te <- incCurrentTime
    insert (ts,te,f) into rs
  write :: Mod -> v -> ()
  write (vs,rs,eq) v = do
    tw <- incCurrentTime
    (tb,vb) <- value at or before tw
    if eq v vb then return else
      insert v into vs at tw
      (tw',v') <- value after tw
      rds <- find readers after tw but before tw' in rs
      remove rds from rs
      insert rds into priority queue
  memo = do
    let table ← new memo table
    return $ \key f -> case (find (table, key, now)) of
      NONE =>
        t s ← advance-time ()
        v ← f ()
        t e ← advance-time ()
        insert ( v,t s ,t e ) into table
        return v
      SOME ( v,t s ,t e ) with ts,ts inside current-time,end-of-memo =>
        undo (current-time, t s ) -- update versions read by memo, delete computations containing this computation
        propagate ( t e )
        return v
  deref (vs,rs,_)= do
    t <- current-time
    (time, v) <- latest value before current-time of vs
    return v
  update (vs,rs,eq) v = do
    (tb,vb) <- earliest value
    if eq v vb then return else
      replace vb with v in vs at tb
      (tw',v') <- value after tw
      dirty readers after tw but before tw' in rs

undo ( t start ,t end ) =
  for each t . t s < t < t e do
    if there is a reader r =( t, , ) then
      delete r from its readers-set and from Q
    if there is a memo entry m =( t, , ) then
      delete m from its table
    if there is a version v =( v t ,t )
      delete version v from its version-set
      dirty all readers between t and earliest version after v
    delete t from time-stamps
propagate dirty_e t =
  for each dirty outgoing edge in the order they were added prioritized by start time has start time before t:
    clear its dirty flag
    recurse on any dirty outgoing edges in the target
    compare the value of the target thunk against the label of the outgoing edge
    if anything is inconsistent:
      remove all its outgoing edges
      re-evaluate the thunk (Adding them back)
    run f with current-time = ts and end-of-memo = te
    current-time ← t s
    undo (current-time, t e )

http://www.cs.cmu.edu/~joshuad/papers/ifsac-jfp/Chen14_implicit_SAC.pdf
http://www.carlssonia.org/ogi/papers/icfp-2002.pdf

http://drum.lib.umd.edu/bitstream/handle/1903/14708/CS-TR-5027.pdf?sequence=1
http://www.ccs.neu.edu/home/amal/papers/impselfadj.pdf
https://arxiv.org/pdf/1503.07792v5.pdf

injecting file changes into the model

files which are in the process of being checked / built
files that throw exceptions when rebuilding.

the previous dependencies determine whether a file is dirty/clean
they also help with pruning unused dependencies

rule "cp input output" - "touch output" will rebuild it

Shake will still keep stale top-level outputs, and their dependencies; they can be deleted with --prune.
However, it will delete intermediate generated files if they are unused.

One of the following must be true:
1) at the end of the rule, this key has written to the file (ownership)
2) a key is guaranteed to have already written the file (weak dependency)
3) this file is never written to by the build system (untracked dependency)
4) someone explicitly gave you permission with trackAllow (hack)

can only omit a build step if all input/output dependencies and the command for that build step exactly match the cached versions in the database

changes:
  syncing to an earlier revision of a file
  changes to commands
  altering the options passed to the compiler in a given build step
  unsuccessful termination of a subprocess after that subprocess has started writing to its output file
  renaming a .c file
all the expected output files exist, and their contents are correct, as specified by the steps or rules required to create them

Shake offers the following guarantee: after a successful invocation of the build tool during which you made no edits, the build will be in a correct state. (If you edit your source files during a build, Bazel makes no guarantee about the correctness of the result of the current build. But it does guarantee that the results of the next build will restore correctness.)

As with all guarantees, there comes some fine print: there are some known ways of getting into an consistent incorrect state with Bazel. We won't guarantee to investigate such problems arising from deliberate attempts to find bugs in the incremental dependency analysis, but we will investigate and do our best to fix all consistent incorrect states arising from normal or "reasonable" use of the build tool.

Correctness: Given an up-to-date system in state X, applying change A and updating the system may result in state Y. Undoing change A and performing an update must return the system to state X.
Modeless: There must not be different ways of building the system that the user must remember in order to accommodate correctness.

Build System
In this paper, a build system is any piece of software that provides facilities
for constructing and parsing the DAG which represents the dependencies
among files in a software project. This paper is not focused on the aspect of
building software related to configuration options as would typically be
handled by software such as autoconf or kconfig, even though some of these
features have been introduced into build systems billed as replacements for
make (which itself does not have such features built-in). When the build
system is invoked, it will input the DAG and current filesystem state, and
output a new DAG and/or files that represent the output of the build.
Update
The update operation is the operation of the build system that actually
compiles and links files that have changed. This is the "Compile" portion of
the Edit-Compile-Test cycle (and optionally the "Test" portion as well,
depending on how automated and modular the tests are).
Gl obal DAG
The global DAG is the entire dependency graph of the software system. This is
the DAG used in a non-recursive make setup, or in any global "top-down" build
system as is common in a make replacement. Figure 1 is an example of a
global DAG, and is the same example as was used to illustrate the problem in
RMCH. Note that the arrows in this graph are actually reversed from the
graph in RMCH. Although we will see later in this paper that the arrows
actually should go "up", in make's view the arrows go "down". Essentially
RMCH displayed how the DAG should look, but was mis-representative of how
the DAG is processed in make.



-- 2. Interleaved execution: the file list action scans the files, runs plausible generating actions untracked (perhaps with orderOnly), and writes a dependency list a-posteriori.
-- 3. Monster rule: A single rule implements all dependency tracking and uses 'parallel' when convenient
-- 4. Weak dependency: sequential ordering of dependencies ensures that all relevant generated files are created before the file list is built
-- 5. Eventual consistency: the filesystem is monitored, regenerating the list on every update; any rules depending on the list are added to a pending queue which is run periodically. Eventually, if all goes well, all files will be generated and the system will stabilize.


# The Shake Model

In order to understand the behaviour of Shake, it is useful to have a mental model of Shake's internal state. To be a little more concrete, let's talk about `File`s which are stored on disk, which have `ModTime` value's associated with them, where `modtime` gives the `ModTime` of a `FilePath` (Shake is actually generalised over all those things). Let's also imagine we have the rule:

    file %> \out -> do
        need [dependency]
        run

So `file` depends on `dependency` and rebuilds by executing the action `run`.

Shake: file is dirty if modtime changed or dependency modtimes changed

If you update an output file, it will rebuild that file, as the `ModTime` of a result is tracked.

Generated files where the generator changes often but the output of the generator for a given input changes rarely
file splitting, where certain rules depend only on part of the file

what we are really doing is comparing the first `ModTime` with the `ModTime` _on disk_ and the list of second `ModTime`'s with those _in `database`_
so we are "injecting" changes into the model (database)

(static) a file will only rebuild at most once per run
(memoryless) on a->b->a, we still rebuild a


A `File` only has at most one `ModTime` per Shake run, since
. We use `Step` for the number of times Shake has run on this project.

_Consequence 1:_ The `ModTime` for a file and the `ModTime` for its dependencies are all recorded in the same run, so they share the same `Step`.


_Consequence 2:_ We only use historical `ModTime` values to compare them for equality with current `ModTime` values. We can instead record the `Step` at which the `ModTime` last changed, assuming all older `Step` values are unequal.

The result is:

    database :: File -> (ModTime, Step, Step, [File])

    valid :: File -> ModTime -> Bool
    valid file mNow =
        mNow == mOld &&
        and [sBuild >= changed (database d) | d <- deps]
        where (mOld, sBuilt, sChanged, deps) = database file
              changed (_, _, sChanged, _) = sChanged

For each `File` we store its most recently recorded `ModTime`, the `Step` at which it was built, the `Step` when the `ModTime` last changed, and the list of dependencies. We now check if the `Step` for this file is greater than the `Step` at which `dependency` last changed. Using the assumptions above, the original formulation is equivalent.

Note that instead of storing one `ModTime` per dependency+1, we now store exactly one `ModTime` plus two small `Step` values.

We still store each file many times, but we reduce that by creating a bijection between `File` (arbitrarily large) and `Id` (small index) and only storing `Id`.

## Implementing the Model

For those who like concrete details, which might change at any point in the future, the relevant definition is in [Development.Shake.Database](https://github.com/ndmitchell/shake/blob/master/Development/Shake/Database.hs#L107):

    data Result = Result
        {result    :: Value   -- the result when last built
        ,built     :: Step    -- when it was actually run
        ,changed   :: Step    -- when the result last changed
        ,depends   :: [[Id]]  -- dependencies
        ,execution :: Float   -- duration of last run
        ,traces    :: [Trace] -- a trace of the expensive operations
        } deriving Show

The differences from the model are:

* `ModTime` became `Value`, because Shake deals with lots of types of rules.
* The dependencies are stored as a list of lists, so we still have access to the parallelism provided by `need`, and if we start rebuilding some dependencies we can do so in parallel.
* We store `execution` and `traces` so we can produce profiling reports.
* I haven't shown the `File`/`Id` mapping here - that lives elsewhere.
* I removed all strictness/`UNPACK` annotations from the definition above, and edited a few comments.

As we can see, the code follows the optimised model quite closely.

## Questions/Answers (Simon Peyton Jones)

> Could you state the invariants of the Shake database?

The invariant on the database is that it forms a DAG - all
dependencies must existing in the graph (lookups never fail) and there
are no cycles.

The invariant on using the database is that before using any
information, you must ensure it is valid. So before looking up the
dependencies you must ensure they have become valid.

There are some attempts at defining rules somewhat like yours in the
paper, in S5.1 (see
http://community.haskell.org/~ndm/downloads/paper-shake_before_building-10_sep_2012.pdf).
It's certainly an area that needs formalising in order to properly
express the properties.

>  Suppose the database contains `file -> (mf, [(di,mdi)])`
>  The file is "clean" if the mod-time on disk of 'file' is 'mf'
>  and the mod-time on disk of each dependency 'di' is 'mdi'.
>
>  Or perhaps the latter sentence should say "if each of the
>  dependencies 'di' is clean, and fst(lookup(di)) = mdi?

Assuming there are no files being changed by the external world while
Shake is working, and that all dependencies are clean before they are
used, these two things are the same. In practice, Shake uses the
second formulation, but hopefully that's just an implementation
detail.

>  A file is "dirty" if it is not clean.

Basically, yes. In reality files have a few more states - see Figure 5
in the paper where Ready = clean and Building = dirty. The other
states correspond to files which are in the process of being checked,
and for files that throw exceptions when rebuilding.

> When 'file' is rebuilt, Shake updates the database with
> `file -> (modtime file, [(dependency, modtime dependency)])`
> But is "modtime file" read from the disk?  That is, is it an
> invariant that, for a clean file, the fst of the tuple is the
> actual on-disk mod-time?

Yes. While running a rule, Shake records the dependencies in an
environment. At the end of that rule, Shake looks at the ondisk
modification time, and records that along with the environment.

> Presumably the list of dependencies may be different than
>  the previous time.

Indeed, the previous dependencies determine whether a file is
dirty/clean, but as soon as the rule starts running they are
discarded.

> "If you update an output file, it will rebuild that file,
>   as the ModTime of a result is tracked".  I did not understand that.

Given a build system that does:

    "output" %> \out -> do
        need ["input"]
        cmd "cp input output"

If you run that, and then run "touch output", the file "output" will
be dirty and a subsequent execution will rebuild it. In Make that
isn't the case, and "output" would still be clean.

## Questions/Answers (mb14)

> I'm still confused with the Shake model.
>
> In you rule `File -(ModTime, [(File, ModTime)]`. Is the time stored for a dependency
>
> 1 - the time the dependency has been last used
>
> 2 - the dependency last modification when the dependency has been used?
>
> For example. Let's say B depends on A and A has been modified yesterday.
>
> If I'm building B today: scenario (1) would be store
>
> database B = (Today, [(A, Today)])
>
> where as scenario (2) would store
>
> database B = (Today, [(A, Yesterday)])
>
> My understanding is scenario 2, in that case, ModTime could be easily replaced by a SHA. However, *Consequence 1*
>
> The ModTime for a file and the ModTime for its dependencies are all recorded in the same run, so they share the same Step
>
> Let's suppose we are using scenario (1).

In the simple model, the time stored for a dependency is the last modification when the dependency has been used. So the semantics are based on scenario 2.

In the complex model, I move to scenario 1, but using some fake notion of Step to be the time.

The key is that I couldn't record only the scenario 2 information in the simple model because I need to know if the time has changed. I solve that in the complex model by storing two Step values, and relying on some assumptions.

> Also, `valid` doesn't seem to be recursive, whereas you would expect an invalid dependency to invalidate all of it's dependees.
Is this assumption wrong or is the recursion is *hidden* in the code.

For valid, I am assuming that before you call valid on a File, you have already called valid on all its dependencies, and if necessary, built them so they have become valid. I had noted that in an earlier draft of this post, but it got lost in editing :(.

Shake will still keep stale top-level outputs, and their dependencies; they can be deleted with --prune.
However, it will delete intermediate generated files if they are unused.

One of the following must be true:
1) at the end of the rule, this key has written to the file (ownership)
2) a key is guaranteed to have already written the file (weak dependency)
3) this file is never written to by the build system (untracked dependency)
4) someone explicitly gave you permission with trackAllow (hack)

can only omit a build step if all input/output dependencies and the command for that build step exactly match the cached versions in the database


changes:
  syncing to an earlier revision of a file
  changes to commands
  altering the options passed to the compiler in a given build step
  unsuccessful termination of a subprocess after that subprocess has started writing to its output file
  renaming a .c file
all the expected output files exist, and their contents are correct, as specified by the steps or rules required to create them

an order-only dependency violation if:

    gen is a generated file
    result depends on gen through deps
    none of result or its direct or order-only dependencies mention gen


Shake enforces hermeticity at the built-in rule level, with the help of tracing for user-level IO actions; this means that anyone writing Shake builtin rules must be aware of synchronization, cleaning, sharing, and rebuild behavior. In particular, Shake uses a single global state dictionary instead of passing multiple versions between functions. This is done to keep the build system within the realm of today's computers, which use a single global state for many operations, such as the filesystem; and also to support network operations, as the physical world cannot be duplicated at will.



Shake provides the "unchanged" flag for this reason; if it is false, you will get a lint error, while if it is true, you will not.

, if a RunClean mode is implemented properly.
- we could preserve the writeFile, and store the initial value in a different location (again, either a file or Shake's key-value store) - this requires a 'move' operation, which is non-hermetic



with the proviso that Shake does not normally store the initial input filesystem, so it will only be able to delete generated files, not undo changes to input files. This proviso is provided to avoid duplicating storage between version control systems and Shake. For 'shake clean' to work exactly as promised, you must properly implement the RunClean mode for each key.

Normal linting, in contrast to the above, simply checks that the build is consistent (that is, the current states of all key-values match those stored in the database). A change from another process (or the user) may create an inconsistency or stale result, as can an unsuccessful build. The build system is sound if it is always consistent after the build tool runs successfully.

The Shake model supports eventually-consistent builds. If you do not use eventual consistency, then a build system is sound. Otherwise, Shake is sound only if the file monitor is enabled, as that will re-run rules in the middle of a run. The simple loop (while (running shake produces changes) {rerun shake}) is also sound. Note though that Shake does not check the convergence of eventually-consistent builds, so these processes may run forever if the system does not converge. A single run of Shake without the file monitor is guaranteed to complete in finite time, but may generate a inconsistent result. Shake's tracing system can warn you if your build system may not converge (in particular, it checks that no key is written to by a rule after it is read by a different rule; this assumes that rules are internally consistent).

In the future, Shake may support sandboxed builds, which creates a separate filesystem tree containing only the inputs and dependencies, and copies only the outputs back into the normal tree. However, tracing is strictly more powerful (in particular, it can record that the build depended on the non-existence of a file), and so this is not a priority.



-- 2. Interleaved execution: the file list action scans the files, runs plausible generating actions untracked (perhaps with orderOnly), and writes a dependency list a-posteriori.
-- 3. Monster rule: A single rule implements all dependency tracking and uses 'parallel' when convenient
-- 4. Weak dependency: sequential ordering of dependencies ensures that all relevant generated files are created before the file list is built
-- 5. Eventual consistency: the filesystem is monitored, regenerating the list on every update; any rules depending on the list are added to a pending queue which is run periodically. Eventually, if all goes well, all files will be generated and the system will stabilize.

