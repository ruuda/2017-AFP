module Paths_ass1Marinus3370798 (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/marinus/stud/afp/ass/ass1/.cabal-sandbox/bin"
libdir     = "/home/marinus/stud/afp/ass/ass1/.cabal-sandbox/lib/x86_64-linux-ghc-7.10.3/ass1Marinus3370798-0.1.0.0-ESgSxZZvlF47pMA4V6VqED"
datadir    = "/home/marinus/stud/afp/ass/ass1/.cabal-sandbox/share/x86_64-linux-ghc-7.10.3/ass1Marinus3370798-0.1.0.0"
libexecdir = "/home/marinus/stud/afp/ass/ass1/.cabal-sandbox/libexec"
sysconfdir = "/home/marinus/stud/afp/ass/ass1/.cabal-sandbox/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "ass1Marinus3370798_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "ass1Marinus3370798_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "ass1Marinus3370798_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "ass1Marinus3370798_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "ass1Marinus3370798_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
