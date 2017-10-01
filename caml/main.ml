external rust : 'a -> 'b -> 'a * 'b = "rusty"

let () =
  for i = 1 to 10000 do
    let a = ref 10 and b = ref 20 in
    let a', b' = rust a b in
    if a <> a || b <> b' then begin
      Printf.printf "%d=%d, %d=%d\n%!" !a !a' !b !b';
      assert false;
    end
  done

