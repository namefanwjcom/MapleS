type $LHelloWorld_3B <class <$Ljava_2Flang_2FObject_3B> {
  &LHelloWorld_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LHelloWorld_3B>>) void,
  &LHelloWorld_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () void}>
type $LForeverLoop_3B <class <$Ljava_2Flang_2FObject_3B> {
  &LForeverLoop_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LForeverLoop_3B>>) void,
  &LForeverLoop_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () void}>
entryfunc &LForeverLoop_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V
javaclass $LForeverLoop_3B <$LForeverLoop_3B> public
func &LForeverLoop_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LForeverLoop_3B>>) void
func &LForeverLoop_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () void
#var $__cinf_Ljava_2Flang_2FString_3B extern <$__class_meta__>
#func &MCC_GetOrInsertLiteral () <* <$Ljava_2Flang_2FString_3B>>
func &LForeverLoop_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LForeverLoop_3B>>) void {
  #funcid 48153
  var %Reg1_R43694 <* <$LForeverLoop_3B>>
  var %Reg1_R57 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg1_R43694 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg1_R43694))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R57) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LForeverLoop_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () void {
  #funcid 48154

  #intrinsiccallwithtype <$LForeverLoop_3B> JAVA_CLINIT_CHECK ()
@label0   #INSTIDX : 0||0000:  goto
  goto @label0
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
