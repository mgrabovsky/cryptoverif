import base, crypto

let init () =
  let var_skS_0= exc_bad_file "skS" skey_from (input_string_from_file "skS") in
  (
   begin
     let token_3 = ref true in
     fun (input_2, input_1) ->
       if (!token_3) then
       begin
         token_3 := false;
         let var_h1_0 = input_2 in 
         let var_h2_0 = input_1 in 
         let list_4 = get_from_table "keytbl"
           (function
               | [tvar_6; tvar_5] -> begin
                 let (tvar_8,tvar_7)=((exc_bad_file "keytbl" id tvar_6),(exc_bad_file "keytbl" pkey_from tvar_5)) in
                 let var_Khost_240 = tvar_8 in 
                 let var_Rkey_0 = tvar_7 in 
                 if (((=) var_Khost_240 var_h2_0)) then (tvar_8,tvar_7) else raise Match_fail
                 end
               | _ -> raise (Bad_file "keytbl")) in
         if list_4 = [] then begin
           raise Match_fail
         end else begin
           let (tvar_8,tvar_7) = rand_list list_4 in
           let var_Khost_240 = tvar_8 in 
           let var_Rkey_0 = tvar_7 in 
           (
             ()
             ,var_Rkey_0, var_h2_0, ((rsassa_pss_sign 8) (concat_pk_str var_Rkey_0 var_h2_0) var_skS_0)
           )
         end
       end
       else raise Bad_call
   end)