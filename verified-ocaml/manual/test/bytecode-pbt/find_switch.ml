(* Find switch instruction targets in pr7253.byte *)
open Interp_extracted

let () =
  let data = Loader.read_file Sys.argv.(1) in
  let sections = Loader.parse_sections data in
  let code = Array.of_list (Loader.load_bytecode_from_sections data sections) in
  let raw_globals = Test_common.load_globals data sections in
  let prims = Test_common.load_prims data sections in
  let (globals, init_heap, init_next_addr) = Test_common.heap_allocate_globals raw_globals in
  let buf = Buffer.create 256 in
  let (heap_ref, next_addr_ref, pending_raise_ref, perform_raise, handler, _get_named_value) =
    Test_common.make_handler ~raw_globals prims buf in
  let s = ref { (initial_state globals) with hp = init_heap; next_addr = init_next_addr } in
  heap_ref := init_heap;
  next_addr_ref := init_next_addr;
  let step_count = ref 0 in
  let history = Array.make 200 0 in
  let hist_idx = ref 0 in
  let rec loop () =
    incr step_count;
    if !step_count > 1000000 then (Printf.printf "STEP LIMIT\n"; exit 0);
    history.(!hist_idx mod 200) <- !s.pc;
    incr hist_idx;
    (match step code !s with
    | Step s' -> s := s'; loop ()
    | Halt _ -> Printf.printf "HALT\nOutput: %S\n" (Buffer.contents buf)
    | Error msg ->
      Printf.printf "ERROR at step %d pc=%d: %s\ntrap_sp=%d stack_len=%d\n"
        !step_count !s.pc (Test_common.sc msg) !s.trap_sp (List.length !s.stack);
      Printf.printf "Output so far: %S\n" (Buffer.contents buf);
      Printf.printf "Last 200 PCs (oldest first):\n";
      for k = 0 to 199 do
        let idx = (!hist_idx + k) mod 200 in
        Printf.printf "%d " history.(idx)
      done;
      Printf.printf "\n"
    | CCall_request (idx, args, cont) ->
      heap_ref := cont.hp;
      next_addr_ref := cont.next_addr;
      pending_raise_ref := None;
      (match handler idx args with
       | Some v ->
         s := { (set_accu cont v) with hp = !heap_ref; next_addr = !next_addr_ref };
         loop ()
       | None ->
         (match !pending_raise_ref with
          | Some exn ->
            let cont' = { cont with hp = !heap_ref; next_addr = !next_addr_ref } in
            (match perform_raise cont' exn with
             | Step s' -> s := s'; loop ()
             | Halt _ -> Printf.printf "HALT\nOutput: %S\n" (Buffer.contents buf)
             | Error msg ->
               Printf.printf "CCALL RAISE ERROR: %s\n" (Test_common.sc msg)
             | CCall_request _ -> Printf.printf "NESTED CCALL\n")
          | None -> Printf.printf "CCALL FAILED\n")))
  in
  loop ()
