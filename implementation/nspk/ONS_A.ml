import base, crypto

let init () =
  let var_A_0= exc_bad_file "idA" id (input_string_from_file "idA") in
  let var_pkS_0= exc_bad_file "pkS" pkey_from (input_string_from_file "pkS") in
  let var_skA_0= exc_bad_file "skA" skey_from (input_string_from_file "skA") in
  (
   begin
     let token_29 = ref true in
     fun (input_28) ->
       if (!token_29) then
       begin
         token_29 := false;
         let var_hostX_0 = input_28 in 
         (
           (
            begin
              let token_33 = ref true in
              fun (input_32, input_31, input_30) ->
                if (!token_33) then
                begin
                  token_33 := false;
                  let var_pkX_0 = input_32 in 
                  if var_hostX_0 = input_31 then
                  begin
                    let var_ms_232 = input_30 in 
                    if ((rsassa_pss_verify 8) (concat_pk_str var_pkX_0 var_hostX_0) var_pkS_0 var_ms_232) then
                    begin
                      let var_Na_233 = (rand_string 8) () in
                      (
                        (
                         begin
                           let token_35 = ref true in
                           fun (input_34) ->
                             if (!token_35) then
                             begin
                               token_35 := false;
                               let var_m_234 = input_34 in 
                               try
                                 let bvar_36=(pk_dec var_m_234 var_skA_0) in
                                 let (bvar_37)=injbot_inv bvar_36 in
                                 let (bvar_38,var_Nb_235,bvar_39)=unconcat_str_str_str bvar_37 in
                                 if bvar_38=var_Na_233 && bvar_39=var_hostX_0 then begin
                                   (
                                     ()
                                     ,(pk_enc ((pad Cryptokit.Padding.length 64) var_Nb_235) var_pkX_0)
                                   )
                                 end
                                 else
                                   raise Match_fail
                               with Match_fail -> 
                                 raise Match_fail
                             end
                             else raise Bad_call
                         end)
                        ,(pk_enc (concat_str_str var_Na_233 var_A_0) var_pkX_0)
                      )
                    end
                    else
                    begin
                      raise Match_fail
                    end
                  end else begin 
                    raise Match_fail
                  end
                end
                else raise Bad_call
            end)
           ,var_A_0, var_hostX_0
         )
       end
       else raise Bad_call
   end)