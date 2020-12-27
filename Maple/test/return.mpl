entryfunc &LHelloWorld_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V
type $LHelloWorld_3B <class <$Ljava_2Flang_2FObject_3B> {
  &LHelloWorld_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LHelloWorld_3B>>) void,
  &LHelloWorld_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () void}>
func &LHelloWorld_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LHelloWorld_3B>>) void
func &LHelloWorld_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () void
var $_C_STR_d9bd4a0c2c2117158ed933ab7468a461 <[4] u64>
#func &MCC_GetOrInsertLiteral () <* <$Ljava_2Flang_2FString_3B>>
func &LHelloWorld_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LHelloWorld_3B>>) void {
  var %Reg1_R43694 <* <$LHelloWorld_3B>>
  var %Reg0_R43694 <* <$LHelloWorld_3B>>
  var %Reg0_R57 <* <$Ljava_2Flang_2FObject_3B>>
  dassign %Reg1_R43694 0 (dread ref %_this)
  dassign %Reg0_R43694 0 (dread ref %Reg1_R43694)
  dassign %Reg0_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg0_R43694))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R57) {}
  return ()

}
func &LHelloWorld_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () void {
  #var %Reg0_R562 <* <$Ljava_2Fio_2FPrintStream_3B>>
  #var %Reg1_R43 <* <$Ljava_2Flang_2FString_3B>>
  #var %L_STR_161334 <* <$Ljava_2Flang_2FString_3B>>

  #dassign %Reg0_R562 0 (dread ref $Ljava_2Flang_2FSystem_3B_7Cout)
  #callassigned &MCC_GetOrInsertLiteral (addrof ptr $_C_STR_d9bd4a0c2c2117158ed933ab7468a461) { dassign %L_STR_161334 0 }
  #dassign %Reg1_R43 0 (dread ptr %L_STR_161334)
  #virtualcallassigned &Ljava_2Fio_2FPrintStream_3B_7Cprintln_7C_28Ljava_2Flang_2FString_3B_29V (dread ref %Reg0_R562, dread ref %Reg1_R43) {}
  javatry {@label0}
  brtrue @label0 (constval i32 0)
  endtry
  #return (constval u64 2147483649)

}
type $Ljava_2Flang_2FObject_3B <class {
  @shadow_24__klass__ i32 private,
  @shadow_24__monitor__ i32 private,
  &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V public constructor (i32) void}>
func &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$Ljava_2Flang_2FObject_3B>>) void {
  var %Reg0_R5147 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg0_R5147 0 (dread ref %_this)
  return ()
}
