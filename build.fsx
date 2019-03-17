#I @".paket/load/net47"
#I @"packages/"

#load @"Zen.FSharp.Compiler.Service.fsx"
#r @"packages/FAKE/tools/FakeLib.dll"
open Fake
open System.IO
open Microsoft.FSharp.Compiler.SourceCodeServices
open Microsoft.FSharp.Compiler

module Array = Microsoft.FSharp.Collections.Array

type FStarFile =
    | Fst of string
    | Fsti of string

type BuildOperation =
    | Extract of FStarFile
    | Realize of FStarFile
    | Include of string

let sources =
    [
        Realize <| Fst "prims";
        Realize <| Fst "FStar.Pervasives";
        Extract <| Fst "Zen.Base";
        Extract <| Fst "Zen.Option";
        Extract <| Fst "Zen.Result";
        Realize <| Fst "Zen.Cost.Realized";
        Extract <| Fst "Zen.Cost.Extracted";
        Extract <| Fst "Zen.Integers";
        Realize <| Fst "FStar.UInt8";
        Realize <| Fst "FStar.UInt32";
        Realize <| Fst "FStar.UInt64";
        Realize <| Fst "FStar.Int64";
        Realize <| Fsti "FStar.Char";
        Realize <| Fsti "Zen.Set";
        Extract <| Fst "Zen.OptionT";
        Extract <| Fst "Zen.ResultT";
        Extract <| Fst "Zen.List";
        Extract <| Fst "Zen.ListBounded";
        Realize <| Fsti "Zen.Array.Base";
        Realize <| Fsti "FStar.String";
        Realize <| Fsti "Zen.Dictionary";
        Extract <| Fst "Zen.Array.Indexed";
        Extract <| Fst "Zen.Types.Extracted";
        Extract <| Fst "Zen.Types.Data";
        Realize <| Fsti "Zen.Types.Realized";
        Realize <| Fsti "Zen.Util";
        Realize <| Fsti "Zen.ContractId";
        Realize <| Fsti "Zen.Asset";
        Extract <| Fst "Zen.Types.Main";
        Realize <| Fsti "Zen.Wallet";
        Realize <| Fsti "Zen.TxSkeleton";
        Extract <| Fst "Zen.Data";
        Extract <| Fst "Zen.ContractReturn";
        Extract <| Fst "Zen.ContractResult";
        Realize <| Fsti "Zen.Hash.Sha3";
        Realize <| Fsti "Zen.Crypto";
        Extract <| Fst "Zen.Hash.Base";
        Realize <| Fsti "Zen.MerkleTree";
        Realize <| Fsti "Zen.Bitcoin";
        Include <| "Zen.Cost";
        Include <| "Zen.Array";
        Include <| "Zen.Types";
        Include <| "Zen.Hash";
    ]

let get_fstar_module_name: FStarFile -> string =
    function
    | Fst src  -> src
    | Fsti src -> src

let to_fstar_fullname: FStarFile -> string =
    function
    | Fst src  -> "fstar/" + src + ".fst"
    | Fsti src -> "fstar/" + src + ".fsti"

let bop_to_fstar_fullname: BuildOperation -> option<string> =
    function
    | Extract src -> Some <| to_fstar_fullname src
    | Realize src -> Some <| to_fstar_fullname src
    | Include src -> None

let handleExtraction: BuildOperation -> list<string> =
    function
    | Extract src -> ["--extract_module"; get_fstar_module_name src]
    | Realize src -> []
    | Include src -> ["--codegen-lib"; src]

let handleBuild: BuildOperation -> list<string> =
    function
    | Extract src -> ["fsharp/Extracted/" + get_fstar_module_name src + ".fs"]
    | Realize src -> ["fsharp/Realized/" + get_fstar_module_name src + ".fs"]
    | Include src -> []

let extractedDir = "fsharp/Extracted"
let binDir = "bin"

let concatMap f ls = List.concat (List.map f ls)

let (++) = Array.append

let getFiles pattern =
  FileSystemHelper.directoryInfo  FileSystemHelper.currentDirectory
  |> FileSystemHelper.filesInDirMatching pattern
  |> Array.map (fun file -> file.FullName)

//let zulibFiles = getFiles "fstar/*.fst" ++ getFiles "fstar/*.fsti"
let zulibFiles =
    List.choose bop_to_fstar_fullname sources
    |> List.toArray
    |> Array.map FileSystemHelper.FullName

let getHints() = getFiles "fstar/*.hints" ++ getFiles "fstar/*.checked"

let zipHints(): unit =
    Fake.ZipHelper.Zip "fstar" "fstar/Hints.zip" <| getHints()

let unzipHints(): unit =
    Fake.ZipHelper.Unzip "fstar" "fstar/Hints.zip"

let clearHints(): unit =
    Fake.FileHelper.DeleteFiles <| getHints()

let runFStar args files =

  let join = Array.reduce (fun a b -> a + " " + b)

  let primsFile = "\"" + FileSystemHelper.currentDirectory + "/fstar/prims.fst" + "\""
  let files = Array.map (fun f -> "\"" + f + "\"") files

  let executable,fstarPath,z3Path =
    if EnvironmentHelper.isLinux then ("mono", "packages/ZFStar/tools/fstar.exe", "packages/zen_z3_linux/output/z3-linux")
    elif EnvironmentHelper.isMacOS then ("mono", "packages/ZFStar/tools/fstar.exe", "packages/zen_z3_osx/output/z3-osx")
    else ("packages/ZFStar/tools/fstar.exe","","packages/zen_z3_windows/output/z3.exe")

  let fstar = [|
    fstarPath;
    "--smt";z3Path;
    "--prims";primsFile;
    "--no_default_includes";
    "--include";"fstar/"; |]
  //printfn "%s" (join (fstar ++ args ++ zulibFiles));
  ProcessHelper.Shell.AsyncExec (executable, join (fstar ++ args ++ files))

Target "Clean" (fun _ ->
  CleanDir extractedDir
  CleanDir binDir
)

Target "RecordHints" (fun _ ->
  let args =
    [| //"--z3refresh";
       //"--verify_all";
       "--record_hints"
       "--cache_checked_modules" |]
  //clearHints();
  //unzipHints();
  let exitCodes = zulibFiles |> Array.map (fun file -> runFStar args [|file|])
                             |> Async.Parallel
                             |> Async.RunSynchronously
  if exitCodes |> Array.forall ((=) 0)
  then zipHints()
  else failwith "recording Zulib hints failed"

)

Target "Verify" (fun _ ->
  let args =
    [| "--use_hints";
       //"--strict_hints";
       "--use_hint_hashes"
       "--cache_checked_modules"
    |]
  clearHints();
  unzipHints();
  let exitCodes = zulibFiles |> Array.map (fun file -> runFStar args [|file|])
                             |> Async.Parallel
                             |> Async.RunSynchronously
  if not (Array.forall (fun exitCode -> exitCode = 0) exitCodes)
    then failwith "Verifying Zulib failed"
)


Target "Extract" (fun _ ->
  let cores = System.Environment.ProcessorCount
  let threads = cores * 2
  let (++) = List.append
  let args =
    [
       "--lax";
       //"--cache_checked_modules"
       //"--use_hints";
       //"--use_hint_hashes";
       "--codegen";"FSharp"
     ] ++ concatMap handleExtraction sources
       ++ ["--odir"; extractedDir]

  let exitCode = runFStar (List.toArray args) zulibFiles
                 |> Async.RunSynchronously

  if exitCode <> 0 then
    failwith "extracting Zulib failed"
)

Target "Build" (fun _ ->

  let files =
    List.toArray (concatMap handleBuild sources)

  let checker = FSharpChecker.Create()

  let frameworkDirectory =
    if EnvironmentHelper.isLinux then ("/usr/lib/mono/4.7-api/")
    elif EnvironmentHelper.isMacOS then ("/Library/Frameworks/Mono.framework/Versions/Current/lib/mono/4.7-api/")
    else ("C:\\Program Files (x86)\\Reference Assemblies\\Microsoft\\Framework\\.NETFramework\\v4.7\\")

  let fw = sprintf "%s%s" frameworkDirectory

  let compileParams =
    [|
      "fsc.exe" ; "-o"; "bin/Zulib.dll"; "-a";
      "--noframework";
      "-r"; fw "mscorlib.dll";
      "-r"; fw "System.Core.dll";
      "-r"; fw "System.dll";
      "-r"; fw "System.Numerics.dll";
      "-r"; "packages/FSharp.Core/lib/net45/FSharp.Core.dll"
      "-r"; "packages/FSharp.Compatibility.OCaml/lib/net45/FSharp.Compatibility.OCaml.dll"
      //"-r"; "../../packages/libsodium-net/lib/Net40/Sodium.dll"
      "-r"; "packages/FSharpx.Collections/lib/net40/FSharpx.Collections.dll"
      "-r"; "packages/BouncyCastle/lib/BouncyCastle.Crypto.dll"
      "-r"; "packages/FsBech32/lib/net45/FsBech32.dll"
    |]

  let messages, exitCode =
    Async.RunSynchronously (checker.Compile (Array.append compileParams files))

  if exitCode <> 0 then
    let errors = Array.filter (fun (msg:FSharpErrorInfo) -> msg.Severity = FSharpErrorSeverity.Error) messages
    printfn "%A" errors
    failwith "building Zulib failed"
    )

Target "Test" (fun _ ->
    let fsharpi (fsx: string) =
        if EnvironmentHelper.isWindows
        then ProcessHelper.Shell.AsyncExec("fsi.exe", fsx)
        else ProcessHelper.Shell.AsyncExec("fsharpi", fsx)

    let tests = getFiles "tests/*.fsx"

    let exitCodes = tests |> Array.map fsharpi
                          |> Async.Parallel
                          |> Async.RunSynchronously
    if not (Array.forall ((=) 0) exitCodes)
    then failwith "One or more tests failed"
)

Target "Default" ( fun _ ->
    Run "Clean"
    Run "Verify"
    Run "Extract"
    Run "Build"
    Run "Test"
    )

(*
"Clean"
  ==> "Verify"
  ==> "Extract"
  ==> "Build"
  ==> "Default"
*)

RunTargetOrDefault "Default"
