let () =
  for i = 1 to 1000 do
    let a = ref 10 and b = ref 20 in
    let a', b' = Rusty.mkpair a b in
    if a <> a || b <> b' then begin
      Printf.printf "%d=%d, %d=%d\n%!" !a !a' !b !b';
      assert false;
    end
  done;
  Printf.printf "%s\n" (Rusty.tostring ("hello", 42));
  match Rusty.somestr 42 with Some s -> Printf.printf "%s\n" s | None -> ()

