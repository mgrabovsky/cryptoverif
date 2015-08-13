import base, crypto

let init () =
  (
   begin
     let token_26 = ref true in
     fun () ->
       if (!token_26) then
       begin
         token_26 := false;
         let var_A_0 = (concat_str_str (get_hostname ()) "A") in 
           output_string_to_file "idA" (id var_A_0);
         try
           let bvar_27=((pk_kgen 1024) ()) in
           let (var_pkA_0,var_skA_0)=id bvar_27 in
           if true then begin
              output_string_to_file "pkA" (pkey_to var_pkA_0);
              output_string_to_file "skA" (skey_to var_skA_0);
             insert_in_table "keytbl" [(id (var_A_0)); (pkey_to (var_pkA_0))];

             (
               ()
               ,var_pkA_0
             )
           end
           else
             raise Match_fail
         with Match_fail -> 
           raise Match_fail
       end
       else raise Bad_call
   end)