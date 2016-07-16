
module Test.Digest(main) where

import Control.Monad
import Development.Shake
import Test.Type


main = shakenCwd test $ \args obj -> do
    if null args then want [obj "Out.txt",obj "Out2.txt"] else want $ map obj args

    obj "Out.txt" %> \out -> do
        txt <- readFile' $ obj "In.txt"
        liftIO $ appendFile out txt

    [obj "Out1.txt",obj "Out2.txt"] &%> \[out1,out2] -> do
        txt <- readFile' $ obj "In.txt"
        liftIO $ appendFile out1 txt
        liftIO $ appendFile out2 txt

    [obj "Bug1.txt",obj "Bug2.txt"] &%> \[out1,out2] -> do
        need [obj "Bug3.txt"]
        writeFile' out1 "X"
        writeFile' out2 "Y"

    "leaf" ~> return ()
    obj "node1.txt" %> \file -> do need ["leaf"]; writeFile' file "x"
    obj "node2.txt" %> \file -> do need [obj "node1.txt"]; liftIO $ appendFile file "x"

    [obj "rewrite1",obj "rewrite2"] &%> \outs -> do
        alwaysRerun
        forM_ outs $ \out -> writeFile' out "rewrite"


test build obj = do
    let outs = take 1 $ map obj ["Out.txt","Out1.txt","Out2.txt"]
    let writeOut x = forM_ outs $ \out -> writeFile out x
    let writeIn = writeFile (obj "In.txt")
    let assertOut x = forM_ outs $ \out -> assertContents out x

    writeOut ""
    writeIn "X"
    build ["--sleep","--digest-and"]
    assertOut "X"

    -- should not involve a hash calculation (sadly no way to test that)
    build ["--sleep","--digest-and"]
    assertOut "X"

    writeIn "X"
    build ["--sleep","--digest-and"]
    assertOut "X"

    writeIn "X"
    build ["--sleep","--digest-or"]
    assertOut "XX"

    writeIn "X"
    build ["--sleep","--digest-and"]
    assertOut "XX"

    build ["--sleep","--digest-and"]
    writeOut "XX"
    build ["--sleep","--digest-and"]
    assertOut "XX"

    build ["--sleep","--digest-and"]
    writeOut "Y"
    build ["--sleep","--digest-and"]
    assertOut "YX"

    writeIn "X"
    build ["--sleep","--digest"]
    assertOut "YX"

    writeIn "Z"
    build ["--sleep","--digest-and-input"]
    assertOut "YXZ"

    build ["--sleep","--digest-and-input"]
    writeOut "YXZ"
    build ["--sleep","--digest-and-input"]
    assertOut "YXZZ"

    writeIn "Q"
    build ["--sleep","--digest-and-input"]
    assertOut "YXZZQ"

    writeIn "Q"
    build ["--sleep","--digest-and-input"]
    assertOut "YXZZQ"

    -- test for #218
    forM_ [("--digest",1),("--digest-and",1),("--digest-or",2),("--digest-and-input",2),("",2)] $ \(flag,count) -> do
        writeFile (obj "node2.txt") "y"
        replicateM_ 2 $ build $ ["node2.txt","--sleep"] ++ [flag | flag /= ""]
        assertContents (obj "node2.txt") $ 'y' : replicate count 'x'

    -- test for #296
    writeFile (obj "Bug3.txt") "X"
    build ["--digest-and-input","Bug1.txt","--sleep"]
    writeFile (obj "Bug3.txt") "Y"
    build ["--digest-and-input","Bug1.txt","--lint"]

    -- test for #427
    build ["rewrite1","--digest-and"]
    build ["rewrite1","--digest-and","--lint","--sleep"]
