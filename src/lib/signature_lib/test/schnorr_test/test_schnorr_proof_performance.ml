open Core_kernel
open Async
open Pickles_types

(* 测试 Schnorr 签名证明性能 *)
let%test_unit "schnorr signature proof performance" =
  let open Pickles.Impls.Step in
  let module T = Internal_Basic in
  
  (* 编译包含 Schnorr 签名的电路 *)
  let _tag, _cache_handle, proof, Pickles.Provers.[ prove ] =
    Pickles.compile 
      ~public_input:(Pickles.Inductive_rule.Input Typ.unit)
      ~auxiliary_typ:Typ.unit
      ~branches:(module Nat.N1)
      ~max_proofs_verified:(module Nat.N0)
      ~name:"schnorr_signature_proof_test"
      ~choices:(fun ~self:_ ->
        [ { identifier = "schnorr_signature_proof"
          ; prevs = []
          ; main =
              (fun _ ->
                (* 创建测试输入 *)
                let _private_key = exists Field.typ ~compute:(fun () -> T.Field.random ()) in
                let message = exists Field.typ ~compute:(fun () -> T.Field.random ()) in
                let public_key = exists Field.typ ~compute:(fun () -> T.Field.random ()) in
                let _signature_r = exists Field.typ ~compute:(fun () -> T.Field.random ()) in
                let signature_s = exists Field.typ ~compute:(fun () -> T.Field.random ()) in
                
                (* 使用 Schnorr 签名验证 *)
                let _verification_result = 
                  make_checked (fun () -> 
                    (* 这里我们模拟 Schnorr 签名验证的核心逻辑 *)
                    let e = 
                      Field.( * ) message (Field.constant (T.Field.of_int 2))
                    in
                    let s_g = 
                      Field.( * ) public_key signature_s
                    in
                    let e_pk = 
                      Field.( * ) public_key e
                    in
                    let result = 
                      Field.( + ) s_g (Field.negate e_pk)
                    in
                    result
                  ) 
                in
                
                { previous_proof_statements = []
                ; public_output = ()
                ; auxiliary_output = ()
                } )
          ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
          }
        ] )
      ()
  in
  
  let module Proof = (val proof) in
  
  Async.printf "=== Schnorr 签名证明性能测试 ===\n" ;
  
  (* 测试证明生成 *)
  let prove_start_time = Time.now () in
  let public_input, (), proof =
    Async.Thread_safe.block_on_async_exn (fun () -> prove ())
  in
  let prove_end_time = Time.now () in
  let prove_duration = Time.diff prove_end_time prove_start_time in
  
  (* 计算证明大小 *)
  let proof_size_words = Obj.reachable_words (Obj.repr proof) in
  let proof_size_bytes = proof_size_words * (Sys.word_size / 8) in
  let proof_size_kb = proof_size_bytes / 1024 in
  
  (* 测试证明验证 *)
  let verify_start_time = Time.now () in
  Or_error.ok_exn
    (Async.Thread_safe.block_on_async_exn (fun () ->
         Proof.verify [ (public_input, proof) ] ) ) ;
  let verify_end_time = Time.now () in
  let verify_duration = Time.diff verify_end_time verify_start_time in
  
  (* 输出结果 *)
  Async.printf "证明生成时间: %s\n" (Time.Span.to_string prove_duration) ;
  Async.printf "证明大小: %d 字节 (%d 字, %d KB)\n" proof_size_bytes proof_size_words proof_size_kb ;
  Async.printf "证明验证时间: %s\n" (Time.Span.to_string verify_duration) ;
  Async.printf "总时间: %s\n" (Time.Span.to_string (Time.Span.( + ) prove_duration verify_duration)) ;
  Async.printf "================================\n\n" ;
  
  (* 验证性能指标 *)
  let prove_time_sec = Time.Span.to_sec prove_duration in
  let verify_time_sec = Time.Span.to_sec verify_duration in
  
  (* 确保证明生成时间在合理范围内 *)
  assert (Float.( > ) prove_time_sec 0.0) ;
  assert (Float.( < ) prove_time_sec 300.0) ; (* 5分钟内应该完成 *)
  
  (* 确保验证时间在合理范围内 *)
  assert (Float.( > ) verify_time_sec 0.0) ;
  assert (Float.( < ) verify_time_sec 60.0) ; (* 1分钟内应该完成验证 *)
  
  (* 确保证明大小合理 *)
  assert (proof_size_bytes > 0) ;
  assert (proof_size_bytes < 100_000_000) ; (* 小于100MB *)