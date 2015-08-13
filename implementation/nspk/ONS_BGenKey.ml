import base, crypto

let init () =
  (
   begin
     let token_11 = ref true in
     fun () ->
       if (!token_11) then
       begin
         token_11 := false;
         let var_B_0 = (concat_str_str (get_hostname ()) "B") in 
           output_string_to_file "idB" (id var_B_0);
         try
           let bvar_12=((pk_kgen 1024) ()) in
           let (var_pkB_0,var_skB_0)=id bvar_12 in
           if true then begin
              output_string_to_file "pkB" (pkey_to var_pkB_0);
              output_string_to_file "skB" (skey_to var_skB_0);
             insert_in_table "keytbl" [(id (var_B_0)); (pkey_to (var_pkB_0))];

             (
               ()
               ,var_pkB_0
             )
           end
           else
             raise Match_fail
         with Match_fail -> 
           raise Match_fail
       end
       else raise Bad_call
   end)