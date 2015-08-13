import base, crypto

let init () =
  let var_B_0= exc_bad_file "idB" id (input_string_from_file "idB") in
  let var_pkS_0= exc_bad_file "pkS" pkey_from (input_string_from_file "pkS") in
  let var_skB_0= exc_bad_file "skB" skey_from (input_string_from_file "skB") in
  (
   begin
     let token_14 = ref true in
     fun (input_13) ->
       if (!token_14) then
       begin
         token_14 := false;
         let var_m_236 = input_13 in 
         try
           let bvar_15=(pk_dec var_m_236 var_skB_0) in
           let (bvar_16)=injbot_inv bvar_15 in
           let (var_Na_237,var_hostY_0)=unconcat_str_str bvar_16 in
           if true then begin
             (
               (
                begin
                  let token_20 = ref true in
                  fun (input_19, input_18, input_17) ->
                    if (!token_20) then
                    begin
                      token_20 := false;
                      let var_pkY_0 = input_19 in 
                      if var_hostY_0 = input_18 then
                      begin
                        let var_ms_238 = input_17 in 
                        if ((rsassa_pss_verify 8) (concat_pk_str var_pkY_0 var_hostY_0) var_pkS_0 var_ms_238) then
                        begin
                          let var_Nb_239 = (rand_string 8) () in
                          (
                            (
                             begin
                               let token_22 = ref true in
                               fun (input_21) ->
                                 if (!token_22) then
                                 begin
                                   token_22 := false;
                                   let var_m3_0 = input_21 in 
                                   try
                                     let bvar_23=(pk_dec var_m3_0 var_skB_0) in
                                     let (bvar_24)=injbot_inv bvar_23 in
                                     let (bvar_25)=(pad_inv Cryptokit.Padding.length) bvar_24 in
                                     if bvar_25=var_Nb_239 then begin
                                       ()
                                     end
                                     else
                                       raise Match_fail
                                   with Match_fail -> 
                                     raise Match_fail
                                 end
                                 else raise Bad_call
                             end)
                            ,(pk_enc (concat_str_str_str var_Na_237 var_Nb_239 var_B_0) var_pkY_0)
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
               ,var_B_0, var_hostY_0
             )
           end
           else
             raise Match_fail
         with Match_fail -> 
           raise Match_fail
       end
       else raise Bad_call
   end)