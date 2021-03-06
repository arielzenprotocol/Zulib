module Zen.Asset

open FStar.Pervasives
open Zen.Types.Extracted
open System
open System.Text
open FStar.UInt32
open FsBech32
open FStar.Pervasives

module Cost = Zen.Cost.Realized
module ContractId = Zen.ContractId

let private filler len =
    32 - len
    |> Array.zeroCreate

let encodedBytesLength = 2 * ContractId.bytesLength

let private getBytes value = BitConverter.GetBytes (value:uint32)

let private getBigEndinanBytes =
    getBytes
    >> if BitConverter.IsLittleEndian
        then Array.rev
        else id

let zeroHash = Array.zeroCreate 32

let zenAsset : asset = 0ul, zeroHash, zeroHash

let private decodeB16Bytes: Prims.string -> option< array<byte> > =
    System.Text.Encoding.ASCII.GetString >> Base16.decode

let parse (value : Prims.string) : Cost.t<asset Native.option, unit> =
    lazy (
        if value = [| 0uy; 0uy |] then
            Native.Some (0u, zeroHash, zeroHash)
        else
          let contractId = ContractId.parse value.[0..encodedBytesLength-1] |> Cost.__force
          match contractId with
          | Native.Some (ver, cHash) ->
              let subType =
                  if Array.length value = encodedBytesLength
                  then Some zeroHash
                  else decodeB16Bytes value.[encodedBytesLength..]

              match subType with
              | Some subType ->
                  Native.Some (ver, cHash, subType)
              | None ->
                  Native.None
          | Native.None ->
              Native.None
    )
    |> Cost.C

let getDefault ((version,cHash) : contractId) : Cost.t<asset, unit> =
    lazy (version, cHash, zeroHash)
    |> Cost.C

let fromSubtypeString ((version,cHash) : contractId) (value : Prims.string) : Cost.t<asset, unit> =
    lazy (
        let n = Array.length value
        let bytes = Array.append value (filler n)
        version, cHash, bytes
    )
    |> Cost.C

let fromSubtypeInt ((version,cHash) : contractId) (value : uint32) : Cost.t<asset, unit> =
    lazy (
        let bytes = Array.append [| 0uy |] (getBigEndinanBytes value)
        let bytes = Array.append bytes (filler (Array.length bytes))
        version, cHash, bytes
    )
    |> Cost.C
