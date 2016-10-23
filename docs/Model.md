# The Pure Shake Model

Shake takes as primitive a notion of correctness based on a mapping from input dictionaries to resultant dictionaries. Conceptually, the world may be represented as a key-value dictionary (for example, a physics model might map (particle name, time) to position and other state), so this is quite generic. In particular Shake assumes that correctness follows "the Shake model", a Haskell library loosely similar to imperative-style Shake programs.

First, we have dictionaries, which we'll represent as functions for now:

    type Dictionary = Key -> Value

Rules are functions on dictionaries:

    type Rule = Dictionary -> Dictionary
			  = Dictionary -> Key -> Value

Need and apply translate as function application:

    apply [a "x"] --> \d k -> a "x" d k

For parallel application, we require that each changed key is changed only once:

    parallel [a,b] --> \d k -> case filter (/= d k) . map (\x -> x d k) $ [a,b] of
        [] -> d k
        [a] -> a
        _ -> undefined

In the real Shake, need and apply have implicit calls to parallel, so they take multiple arguments.

External commands as well as liftIO etc. translate as pure Haskell functions on the dictionary:

    cmd $ "gcc a.c -o a.o" --> \d k -> if k == "a.o" then gcc (d "a.c") else d k

Reading a file is a key lookup:

    readFile "x" --> d "x"

Monadic computation translates as composition (Haskell values are erased; if they are relevant they can be stored in the dictionary):

    a >> b --> \d k -> let d' = a d in b d' k

Default rules for source files translate as identity:

    need [source_file] --> id

# Hermetic Builds

The pure model alone does not constitute Shake, as Shake does not actually use a pure `Key -> Value` dictionary type. One can think of Shake as a library providing the pure model on top of an impure world. Most values are stored directly on the filesystem, with only tracking information in Shake's internal database. In particular, Shake uses a finite-map model with stamps; a dictionary is an unordered set of (key,stamp) pairs, with the stamps loosely corresponding with the actual external value.

We can summarize execution by the sets of input and output (key,stamp) pairs. The build system is said to be hermetic if the execution trace uniquely determines the external filesystem. There are known non-hermetic examples, e.g. where you are using timestamps and an archiver overwrites with the exact timestamp but a different file. In general the solution to hermeticity failures is to avoid doing whatever made it non-hermetic. Using strong hashes as stamps should avoid almost all problems, at the expense of some performance.

# Incremental changes

The world (input dictionary) is not static, so we incrementalize the model. We want to have correct incremental builds for hermetic systems where all changes are registered, in that they vaguely match the pure model or a from-scratch build. Alternately expressed, given state X, change A with inverse A', and updating operation U, we want 
XAUA'U = XAA'U = XU

Separately, we want to minimize the number of update operations U available, ideally to just 1 command that does everything. But there are always a few extensions that seem necessary:
1) partial updates, so that only a few files are rebuilt
2) touch, which marks the current values as up-to-date
3) cleaning, where all updates are discarded and the system is restored to its initial condition
4) queries, where you just want to know what could change

# Rules

To have something to incrementalize, we start by introducing a notion of "rule", explicitly dividing up the overall input-output function into the composition of lots of small functions using 'parallel' or '.'. Rules can be as coarse or as fine as necessary, but we of course prefer smaller rules since they often allow more work to be skipped. Following Nominal Adapton (or maybe just Haskell's 'let' syntax), we also allow rules to be assigned names so that work can be shared. Shake allows names to be any serializable Haskell ADT and includes an extensible default ADT. Traces then have an acyclic data structure that looks like

	data Trace = Trace (Map Input Stamp) (Map Output Stamp) | Parallel [Trace] | Sequential [Trace] | Named Name
	data Traces = Traces { root :: Name, Map Name Trace }

Rules can take many forms, but they must record an accurate trace of input/output keys and stamps. To implement this, Shake requires that named rules return their trace after execution (via accumulation in a writer monad). Individual commands may run in a separate process under a tracing monitor which computes this information and adds it, or they can be declared using specific functions (Shake includes a library of common operations such as reading or copying files which do proper tracing). Shake also supports a "tracing lint mode", which traces an operation and verifies that the changes match a pre-computed set of declared changes. The tracing system is incomplete at present, e.g. it does not record absent files; this is OK so long as the used but unrecorded values are consistent over all Shake runs.

We depict traces as a graph; names are diamonds, sequential traces are squares, parallel traces are circles, and the final key-value pairs are a house-triangle combination. Our dependencies go from top to bottom, so that "top-level" commands are actually on the top. There is no inner/outer layer separation.

For example, the trace of the sum computation given in the Adapton paper:

![Graph](https://cdn.rawgit.com/Mathnerd314/shake/devel-new/docs/Model.svg)

# Modifiables

Looking at our keys, most will only take one value over the full trace. We thus maintain an index from keys to (rules, stamps) so that they do not have to be constantly passed around. The list of rules for which a certain value holds can be optimized using the DAG structure of rule names to only store the rules that output values.

However, Shake goes further because we don't want to keep multiple versions of files around in the main system. E.g., considering an action such as

    do
      (n :: Int) <- read <$> readFile "a"
      writeFile "a" (show $ n + 1)
      (n' :: Int) <- read <$> readFile "a"

we would have to store both values of n (so as to avoid seeing n+2). Solutions:
- (redirected reads): we can copy the initial file elsewhere, then change the read call to read from that file
- (redirected writes): we can preserve the initial file on-disk, and change the write to store it elsewhere
- (error): we can detect this situation and disallow it, forcing users to do one of the above

Erroring is the best option, since the build system developer must then explicitly pick which file to redirect. So we error on a key read if Shake hasn't already written the key; in this example the first read. Of course, this would mean that Shake can't read any external input, so we have special operations to create a key as input or copied input, with associated checks to ensure they're used correctly (input: cannot change during the run; copied input: copy cannot change during run, input is re-copied if changed by external program, moved back if cleaned).

There's a similar problem with double writes, where we lose the ability to re-run the build system. Again we want to error out if a key is written twice, so that the build system developer can make the decision of where else to store the first or second value. Similarly, we also want to give an (optional) data loss warning if a generated file already exists when the rule declares that it's about to write to it. (Post-declared files have already been overwritten by the time Shake gets to them, so they can still cause an error, but there's no way to recover) So all these are also handled by special operations which check for an existing rule and then do the approprate thing if there's no rule. And sometimes between-run persistence is actually desired, e.g. when command-line options change a config file for all future runs, which we solve by adding an operation for a "sticky" read.

On the other hand, sometimes it might useful to allow multiple values. Part of it's just being general. Maybe the build system is so complex that using a content-addressed store for files makes sense. We also want multiple values so we can store previous runs for posterity; e.g. inject changes then immediately rollback. And of course there's the whole substitutes thing.

The hard part is using the rule trace DAG to determine a proper "logical time" so we can direct the reads/writes appropriately. Maybe there's a standard algorithm that I'm missing; do probabilistic tries help at all?

# Algorithm

The simple algorithm just follows demands down, starting from each top-level demanded rule. 
We look at the traces:
- for a name, we check to see if it's already been proceseed, otherwise process its trace and re-execute if out of date (typically we can only really enter named rules, so the below ones will begin execution at the name rather than the part of the trace)
- for a (parallel|sequential) trace, we process (in parallel|sequentially) and re-execute if any are out-of-date
- for an actual trace, we check that each input matches its stamp, and optionally that each output matches as well (since typically only one rule outputs and so stamp never changes)

A better algorithm keeps track of which rules demanded which inputs when and propagates changes upwards from that, so that the demand traversal can then skip looking at most of the graph, but it's complex keeping track of all that.

We lock each key while building, so that a key is only being built once at any given time. The simple algorithm ensures that only valid dependencies are being executed; the better one should as well.

An unrecoverable build exception is treated as propagating the exception to all parents. A named rule is only considered to be executed once the trace is stored in Shake's database; otherwise it's a partial or unsuccessful run. There's a small window between when a file is written and when it is recorded in the graph as changed during which it could be rewritten again and be out-of-date.
