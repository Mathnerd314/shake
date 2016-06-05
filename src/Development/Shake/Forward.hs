{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, Rank2Types, ScopedTypeVariables, MultiParamTypeClasses #-}

-- | A module for producing forward-defined build systems, in contrast to standard backwards-defined
--   build systems such as shake. Based around ideas from <https://code.google.com/p/fabricate/ fabricate>.
--   As an example:
--
-- @
-- import "Development.Shake"
-- import "Development.Shake.Forward"
-- import "Development.Shake.FilePath"
--
-- main = 'shakeArgsForward' 'shakeOptions' $ do
--     contents <- 'readFileLines' \"result.txt\"
--     'cache' $ 'cmd' \"tar -cf result.tar\" contents
-- @
--
--   Compared to backward-defined build systems (such as normal Shake), forward-defined build
--   systems tend to be simpler for simple systems (less boilerplate, more direct style), but more
--   complex for larger build systems (requires explicit parallelism, explicit sharing of build products,
--   no automatic command line targets). As a general approach for writing forward-defined systems:
--
-- * Figure out the sequence of system commands that will build your project.
--
-- * Write a simple 'Action' that builds your project.
--
-- * Insert 'cache' in front of most system commands.
--
-- * Replace most loops with 'forP', where they can be executed in parallel.
--
-- * Where Haskell performs real computation, if zero-build performance is insufficient, use 'cacheAction'.
--
--   All forward-defined systems use 'AutoDeps', which requires @fsatrace@ to be on the @$PATH@.
--   You can obtain @fsatrace@ from <https://github.com/jacereda/fsatrace>.
module Development.Shake.Forward(
    shakeForward, shakeArgsForward,
    forwardOptions, forwardRule,
    cache, cacheAction
    ) where

import Development.Shake
import Development.Shake.Core
import Development.Shake.Rule
import Development.Shake.Command
import Development.Shake.FilePath
import Data.Either
import Data.List.Extra
import Control.Exception.Extra
import Numeric

-- | Run a forward-defined build system.
shakeForward :: ShakeOptions -> Action () -> IO ()
shakeForward opts act = shake (forwardOptions opts) (forwardRule act)

-- | Run a forward-defined build system, interpretting command-line arguments.
shakeArgsForward :: ShakeOptions -> Action () -> IO ()
shakeArgsForward opts act = shakeArgs (forwardOptions opts) (forwardRule act)

-- | Given an 'Action', turn it into a 'Rules' structure which runs in forward mode.
forwardRule :: Action () -> Rules ()
forwardRule act = do
    rule $ \(ForwardQ k) -> Just $ do
        res <- runForward k
        case res of
            Nothing -> liftIO $ errorIO "Failed to find action name"
            Just act -> act
        return $ ForwardA ()
    action act

-- | Given a 'ShakeOptions', set the options necessary to execute in forward mode.
forwardOptions :: ShakeOptions -> ShakeOptions
forwardOptions opts = opts{shakeCommandOptions=[AutoDeps]}

-- | Apply caching to an external command.
cache :: (forall r . CmdArguments r => r) -> Action ()
cache cmd = do
    let args :: [Either CmdOption String] = cmd
    let isDull ['-',x] = True; isDull _ = False
    let name = head $ filter (not . isDull) (drop 1 $ rights args) ++ ["unknown"]
    cacheAction ("command " ++ toStandard name ++ " #" ++ upper (showHex (abs $ hash $ show args) "")) cmd
