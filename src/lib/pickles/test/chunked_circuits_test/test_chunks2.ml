open Core_kernel
open Pickles_types
open Pickles.Impls.Step

let () = Pickles.Backend.Tick.Keypair.set_urs_info []

let () = Pickles.Backend.Tock.Keypair.set_urs_info []

let test () =
  let test_start_time = Sys.time () in
  let tag, _cache_handle, proof, Pickles.Provers.[ prove ] =
    Pickles.compile ~public_input:(Pickles.Inductive_rule.Input Typ.unit)
      ~auxiliary_typ:Typ.unit
      ~branches:(module Nat.N1)
      ~max_proofs_verified:(module Nat.N0)
      ~num_chunks:2 ~override_wrap_domain:N1 ~name:"chunked_circuits"
      ~choices:(fun ~self:_ ->
        [ { identifier = "2^16"
          ; prevs = []
          ; main =
              (fun _ ->
                let fresh_zero () =
                  exists Field.typ ~compute:(fun _ -> Field.Constant.zero)
                in
                (* Remember that each of these counts for *half* a row, so we
                   need 2^17 of them to fill 2^16 rows.
                *)
                for _ = 0 to 1 lsl 17 do
                  ignore (Field.mul (fresh_zero ()) (fresh_zero ()) : Field.t)
                done ;
                (* We must now appease the permutation argument gods, to ensure
                   that the 7th permuted column has polynomial degree larger
                   than 2^16, and thus that its high chunks are non-zero.
                   Suckiness of linearization strikes again!
                *)
                let fresh_zero = fresh_zero () in
                Impl.assert_
                  (Raw
                     { kind = Generic
                     ; values =
                         [| fresh_zero
                          ; fresh_zero
                          ; fresh_zero
                          ; fresh_zero
                          ; fresh_zero
                          ; fresh_zero
                          ; fresh_zero
                         |]
                     ; coeffs = [||]
                     } ) ;
                { previous_proof_statements = []
                ; public_output = ()
                ; auxiliary_output = ()
                } )
          ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
          }
        ] )
      ()
  in
  let first_compile_end_time = Sys.time () in
  let first_compile_duration = first_compile_end_time -. test_start_time in
  Printf.printf "First circuit compilation time: %f seconds\n" first_compile_duration ;
  
  let module Requests = struct
    type _ Snarky_backendless.Request.t +=
      | Proof :
          (Nat.N0.n, Nat.N0.n) Pickles.Proof.t Snarky_backendless.Request.t

    let handler (proof : _ Pickles.Proof.t)
        (Snarky_backendless.Request.With { request; respond }) =
      (* let start_time = Sys.time () in *)
      let result = match request with
        | Proof ->
            respond (Provide proof)
        | _ ->
            respond Unhandled
      in
      (* let end_time = Sys.time () in
      let duration = end_time -. start_time in *)
      (* Printf.printf "Request duration: %f seconds\n" duration ; *)
      result
  end in
  (* force vk creation  *)
  let vk_start_time = Sys.time () in
  let _vk =
    Async.Thread_safe.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled tag )
  in
  let vk_end_time = Sys.time () in
  let vk_duration = vk_end_time -. vk_start_time in
  Printf.printf "First VK creation time: %f seconds\n" vk_duration ;
  
  let tag2, _cache_handle, recursive_proof, Pickles.Provers.[ recursive_prove ]
      =
    Pickles.compile ~public_input:(Pickles.Inductive_rule.Input Typ.unit)
      ~auxiliary_typ:Typ.unit
      ~branches:(module Nat.N1)
      ~max_proofs_verified:(module Nat.N1)
      ~name:"recursion over chunks"
      ~choices:(fun ~self:_ ->
        [ { identifier = "recurse over 2^17"
          ; prevs = [ tag ]
          ; main =
              (fun _ ->
                let proof =
                  exists (Typ.prover_value ()) ~request:(fun () ->
                      Requests.Proof )
                in
                { previous_proof_statements =
                    [ { public_input = ()
                      ; proof
                      ; proof_must_verify = Boolean.true_
                      }
                    ]
                ; public_output = ()
                ; auxiliary_output = ()
                } )
          ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
          }
        ] )
      ()
  in
  let second_compile_end_time = Sys.time () in
  let second_compile_duration = second_compile_end_time -. vk_end_time in
  Printf.printf "Second circuit compilation time: %f seconds\n" second_compile_duration ;
  
  (* force vk creation  *)
  let vk2_start_time = Sys.time () in
  let _vk =
    Async.Thread_safe.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled tag2 )
  in
  let vk2_end_time = Sys.time () in
  let vk2_duration = vk2_end_time -. vk2_start_time in
  Printf.printf "Second VK creation time: %f seconds\n" vk2_duration ;
  
  let module Proof = (val proof) in
  let module Recursive_proof = (val recursive_proof) in
  
  let test_prove_start_time = Sys.time () in
  let test_prove () =
    let start_time = Sys.time () in
    let public_input, (), proof =
      Async.Thread_safe.block_on_async_exn (fun () -> prove ())
    in
    let proof_size_words = Obj.reachable_words (Obj.repr proof) in
    let proof_size_bytes = proof_size_words * (Sys.word_size / 8) in
    let proof_size_kb = proof_size_bytes / 1024 in
    Printf.printf "Proof size: %d bytes (%d words, %d KB)\n" proof_size_bytes proof_size_words proof_size_kb ;
    let end_time = Sys.time () in
    let duration = end_time -. start_time in
    Printf.printf "Prove execution time: %f seconds\n" duration ;
    
    let verify_start_time = Sys.time () in
    Or_error.ok_exn
      (Async.Thread_safe.block_on_async_exn (fun () ->
           Proof.verify [ (public_input, proof) ] ) ) ;
    let verify_end_time = Sys.time () in
    let verify_duration = verify_end_time -. verify_start_time in
    Printf.printf "Verify execution time: %f seconds\n" verify_duration ;
    
    let recursive_prove_start_time = Sys.time () in
    let public_input, (), proof =
      Async.Thread_safe.block_on_async_exn (fun () ->
          recursive_prove ~handler:(Requests.handler proof) () )
    in
    let proof_size_words = Obj.reachable_words (Obj.repr proof) in
    let proof_size_bytes = proof_size_words * (Sys.word_size / 8) in
    let proof_size_kb = proof_size_bytes / 1024 in
    Printf.printf "Recursive proof size: %d bytes (%d words, %d KB)\n" proof_size_bytes proof_size_words proof_size_kb ;
    let recursive_prove_end_time = Sys.time () in
    let recursive_prove_duration = recursive_prove_end_time -. recursive_prove_start_time in
    Printf.printf "Recursive prove execution time: %f seconds\n" recursive_prove_duration ;
    
    let recursive_verify_start_time = Sys.time () in
    Or_error.ok_exn
      (Async.Thread_safe.block_on_async_exn (fun () ->
           Recursive_proof.verify [ (public_input, proof) ] ) ) ;
    let recursive_verify_end_time = Sys.time () in
    let recursive_verify_duration = recursive_verify_end_time -. recursive_verify_start_time in
    Printf.printf "Recursive verify execution time: %f seconds\n" recursive_verify_duration ;
  in
  test_prove () ;
  let test_prove_end_time = Sys.time () in
  let test_prove_duration = test_prove_end_time -. test_prove_start_time in
  Printf.printf "Test prove total time: %f seconds\n" test_prove_duration ;
  
  let total_test_time = test_prove_end_time -. test_start_time in
  Printf.printf "Total test time (including compilation): %f seconds\n" total_test_time

let () =
  test () ;
  Alcotest.run "Chunked circuit"
    [ ("2^16", [ ("prove and verify", `Quick, test) ]) ]
