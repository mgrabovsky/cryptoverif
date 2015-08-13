import base, crypto

let init () =
  (
   begin
     let token_9 = ref true in
     fun () ->
       if (!token_9) then
       begin
         token_9 := false;
         try
           let bvar_10=((pk_kgen 1024) ()) in
           let (var_pkS_0,var_skS_0)=id bvar_10 in
           if true then begin
              output_string_to_file "pkS" (pkey_to var_pkS_0);
              output_string_to_file "skS" (skey_to var_skS_0);
             (
               ()
               ,var_pkS_0
             )
           end
           else
             raise Match_fail
         with Match_fail -> 
           raise Match_fail
       end
       else raise Bad_call
   end)