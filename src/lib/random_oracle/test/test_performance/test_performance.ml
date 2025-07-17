(* 简单的性能测试脚本 *)
open Core_kernel

(* 导入必要的模块 *)
module Random_oracle = Random_oracle

(* 时间测量函数 *)
let time_function name f iterations =
  let start_time = Unix.gettimeofday () in
  for i = 1 to iterations do
    ignore (f ())
  done;
  let end_time = Unix.gettimeofday () in
  let total_time = end_time -. start_time in
  let avg_time = total_time /. Float.of_int iterations in
  Printf.printf "%s:\n" name;
  Printf.printf "  总时间: %.6f 秒\n" total_time;
  Printf.printf "  平均时间: %.6f 秒\n" avg_time;
  Printf.printf "  总调用次数: %d\n" iterations;
  Printf.printf "  每秒调用次数: %.2f\n\n" (Float.of_int iterations /. total_time)

(* 主测试函数 *)
let run_performance_test () =
  let open Pickles.Impls.Step in
  let module T = Internal_Basic in
  
  (* 生成测试数据 *)
  let test_data = List.init 1000 ~f:(fun _ ->
    let x = T.Field.random () in
    let y = T.Field.random () in
    (x, y)
  ) in
  
  let iterations = 100 in
  
  (* 测试 make_checked 性能 *)
  let checked_hash (x, y) =
    make_checked (fun () -> Random_oracle.Checked.hash [| x; y |])
  in
  
  (* 测试普通 hash 性能 *)
  let unchecked_hash (x, y) =
    Random_oracle.hash [| x; y |]
  in
  
  Printf.printf "=== 随机预言机性能测试 ===\n\n";
  
  (* 预热 *)
  Printf.printf "预热中...\n";
  List.iter test_data ~f:(fun data ->
    ignore (checked_hash data);
    ignore (unchecked_hash data)
  );
  Printf.printf "预热完成\n\n";
  
  (* 测试 make_checked 性能 *)
  time_function "make_checked 哈希函数" 
    (fun () -> 
      List.iter test_data ~f:(fun data ->
        ignore (checked_hash data)
      )
    ) 
    iterations;
  
  (* 测试普通 hash 性能 *)
  time_function "普通哈希函数" 
    (fun () -> 
      List.iter test_data ~f:(fun data ->
        ignore (unchecked_hash data)
      )
    ) 
    iterations;
  
  (* 验证结果一致性 *)
  Printf.printf "验证结果一致性...\n";
  let sample_data = List.take test_data 10 in
  List.iter sample_data ~f:(fun (x, y) ->
    let checked_result = checked_hash (x, y) in
    let unchecked_result = unchecked_hash (x, y) in
    if not (T.Field.equal checked_result unchecked_result) then
      failwith "结果不一致！"
  );
  Printf.printf "结果一致性验证通过\n"

(* 详细性能分析 *)
let run_detailed_analysis () =
  let open Pickles.Impls.Step in
  let module T = Internal_Basic in
  
  let iterations = 50 in
  let data_sizes = [10; 50; 100; 500; 1000] in
  
  Printf.printf "=== 详细性能分析 ===\n\n";
  
  List.iter data_sizes ~f:(fun size ->
    Printf.printf "数据大小: %d 个字段对\n" size;
    
    let test_data = List.init size ~f:(fun _ ->
      let x = T.Field.random () in
      let y = T.Field.random () in
      (x, y)
    ) in
    
    (* 测试 make_checked *)
    let start_time = Unix.gettimeofday () in
    for i = 1 to iterations do
      List.iter test_data ~f:(fun (x, y) ->
        ignore (make_checked (fun () -> Random_oracle.Checked.hash [| x; y |]))
      )
    done;
    let checked_time = Unix.gettimeofday () -. start_time in
    
    (* 测试普通 hash *)
    let start_time = Unix.gettimeofday () in
    for i = 1 to iterations do
      List.iter test_data ~f:(fun (x, y) ->
        ignore (Random_oracle.hash [| x; y |])
      )
    done;
    let unchecked_time = Unix.gettimeofday () -. start_time in
    
    Printf.printf "  make_checked 总时间: %.6f 秒\n" checked_time;
    Printf.printf "  普通 hash 总时间: %.6f 秒\n" unchecked_time;
    
    let ratio = checked_time /. unchecked_time in
    Printf.printf "  性能比率 (checked/unchecked): %.2fx\n" ratio;
    Printf.printf "  每次哈希平均时间:\n";
    Printf.printf "    make_checked: %.6f 秒\n" (checked_time /. Float.of_int (iterations * size));
    Printf.printf "    普通 hash: %.6f 秒\n" (unchecked_time /. Float.of_int (iterations * size));
    Printf.printf "\n"
  )

(* 内存使用分析 *)
let run_memory_analysis () =
  let open Pickles.Impls.Step in
  let module T = Internal_Basic in
  
  let iterations = 100 in
  let data_size = 500 in
  
  Printf.printf "=== 内存使用分析 ===\n\n";
  
  let test_data = List.init data_size ~f:(fun _ ->
    let x = T.Field.random () in
    let y = T.Field.random () in
    (x, y)
  ) in
  
  (* 强制垃圾回收 *)
  Gc.full_major ();
  let initial_memory = Gc.stat () in
  
  (* 测试 make_checked 内存使用 *)
  for i = 1 to iterations do
    List.iter test_data ~f:(fun (x, y) ->
      ignore (make_checked (fun () -> Random_oracle.Checked.hash [| x; y |]))
    )
  done;
  
  Gc.full_major ();
  let checked_memory = Gc.stat () in
  
  (* 测试普通 hash 内存使用 *)
  for i = 1 to iterations do
    List.iter test_data ~f:(fun (x, y) ->
      ignore (Random_oracle.hash [| x; y |])
    )
  done;
  
  Gc.full_major ();
  let unchecked_memory = Gc.stat () in
  
  Printf.printf "初始内存使用: %.2f MB\n" (Float.of_int initial_memory.Gc.live_words *. 8.0 /. 1024.0 /. 1024.0);
  Printf.printf "make_checked 后内存使用: %.2f MB\n" (Float.of_int checked_memory.Gc.live_words *. 8.0 /. 1024.0 /. 1024.0);
  Printf.printf "普通 hash 后内存使用: %.2f MB\n" (Float.of_int unchecked_memory.Gc.live_words *. 8.0 /. 1024.0 /. 1024.0);
  
  let checked_increase = checked_memory.Gc.live_words - initial_memory.Gc.live_words in
  let unchecked_increase = unchecked_memory.Gc.live_words - initial_memory.Gc.live_words in
  
  Printf.printf "make_checked 内存增长: %.2f MB\n" (Float.of_int checked_increase *. 8.0 /. 1024.0 /. 1024.0);
  Printf.printf "普通 hash 内存增长: %.2f MB\n" (Float.of_int unchecked_increase *. 8.0 /. 1024.0 /. 1024.0)

(* 主函数 *)
let () =
  Printf.printf "开始随机预言机性能测试...\n\n";
  
  (* 运行基本性能测试 *)
  run_performance_test ();
  
  (* 运行详细分析 *)
  run_detailed_analysis ();
  
  (* 运行内存分析 *)
  run_memory_analysis ();
  
  Printf.printf "性能测试完成！\n" 