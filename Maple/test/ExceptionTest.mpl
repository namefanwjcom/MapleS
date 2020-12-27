type $LBaseException_3B <class <$Ljava_2Flang_2FThrowable_3B> {
  &LBaseException_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LBaseException_3B>>) void}>
type $LDerivedException1_3B <class <$LBaseException_3B> {
  &LDerivedException1_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LDerivedException1_3B>>) void}>
type $LDerivedException2_3B <class <$LBaseException_3B> {
  &LDerivedException2_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LDerivedException2_3B>>) void}>
type $LDerivedException3_3B <class <$LBaseException_3B> {
  &LDerivedException3_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LDerivedException3_3B>>) void}>
type $LExceptionTest_3B <class <$Ljava_2Flang_2FObject_3B> {
  &LExceptionTest_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LExceptionTest_3B>>) void,
  &LExceptionTest_3B_7CTestMain_7C_28I_29I public static (i32) i32,
  &LExceptionTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32}>
type $Ljava_2Flang_2FThrowable_3B <class <$Ljava_2Flang_2FObject_3B> {}>
entryfunc &LExceptionTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V
javaclass $LBaseException_3B <$LBaseException_3B>
javaclass $LDerivedException1_3B <$LDerivedException1_3B>
javaclass $LDerivedException2_3B <$LDerivedException2_3B>
javaclass $LDerivedException3_3B <$LDerivedException3_3B>
javaclass $LExceptionTest_3B <$LExceptionTest_3B> public
func &LBaseException_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LBaseException_3B>>) void
func &LDerivedException1_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LDerivedException1_3B>>) void
func &LDerivedException2_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LDerivedException2_3B>>) void
func &LDerivedException3_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LDerivedException3_3B>>) void
func &LExceptionTest_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LExceptionTest_3B>>) void
func &LExceptionTest_3B_7CTestMain_7C_28I_29I public static (var %Reg4_I i32) i32
func &LExceptionTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32
#var $__cinf_Ljava_2Flang_2FString_3B extern <$__class_meta__>
#func &MCC_GetOrInsertLiteral () <* <$Ljava_2Flang_2FString_3B>>
func &LBaseException_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LBaseException_3B>>) void {
  #funcid 48153
  var %Reg1_R43699 <* <$LBaseException_3B>>
  var %Reg1_R510 <* <$Ljava_2Flang_2FThrowable_3B>>

  dassign %Reg1_R43699 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R510 0 (retype ref <* <$Ljava_2Flang_2FThrowable_3B>> (dread ref %Reg1_R43699))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R510) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LDerivedException1_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LDerivedException1_3B>>) void {
  #funcid 48154
  var %Reg1_R43701 <* <$LDerivedException1_3B>>
  var %Reg1_R43699 <* <$LBaseException_3B>>

  dassign %Reg1_R43701 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R43699 0 (retype ref <* <$LBaseException_3B>> (dread ref %Reg1_R43701))
  callassigned &LBaseException_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R43699) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LDerivedException2_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LDerivedException2_3B>>) void {
  #funcid 48155
  var %Reg1_R43703 <* <$LDerivedException2_3B>>
  var %Reg1_R43699 <* <$LBaseException_3B>>

  dassign %Reg1_R43703 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R43699 0 (retype ref <* <$LBaseException_3B>> (dread ref %Reg1_R43703))
  callassigned &LBaseException_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R43699) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LDerivedException3_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LDerivedException3_3B>>) void {
  #funcid 48156
  var %Reg1_R43705 <* <$LDerivedException3_3B>>
  var %Reg1_R43699 <* <$LBaseException_3B>>

  dassign %Reg1_R43705 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R43699 0 (retype ref <* <$LBaseException_3B>> (dread ref %Reg1_R43705))
  callassigned &LBaseException_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R43699) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LExceptionTest_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LExceptionTest_3B>>) void {
  #funcid 48157
  var %Reg1_R43707 <* <$LExceptionTest_3B>>
  var %Reg1_R57 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg1_R43707 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg1_R43707))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R57) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LExceptionTest_3B_7CTestMain_7C_28I_29I public static (var %Reg4_I i32) i32 {
  #funcid 48158
  var %Reg0_I i32
  var %Reg2_I i32
  var %Reg0_R43700 <* <$LDerivedException1_3B>>
  var %Reg0_R510 <* <$Ljava_2Flang_2FThrowable_3B>>
  var %Reg0_R43702 <* <$LDerivedException2_3B>>
  var %Reg0_R43704 <* <$LDerivedException3_3B>>
  var %Reg3_R43700 <* <$LDerivedException1_3B>>
  var %Reg3_R43702 <* <$LDerivedException2_3B>>

  #intrinsiccallwithtype <$LExceptionTest_3B> JAVA_CLINIT_CHECK ()
  #INSTIDX : 0||0000:  iconst_0
  dassign %Reg0_I 0 (constval i32 0)
  #INSTIDX : 1||0001:  istore_1
  dassign %Reg2_I 0 (dread i32 %Reg0_I)
  javatry { @label2 @label3 }
  #INSTIDX : 2||0002:  iload_0
  #INSTIDX : 3||0003:  bipush
  dassign %Reg0_I 0 (constval i32 10)
  #INSTIDX : 5||0005:  if_icmplt
  brtrue @label0 (lt i32 i32 (dread i32 %Reg4_I, dread i32 %Reg0_I))
  #INSTIDX : 8||0008:  new
  #intrinsiccallwithtype <$LDerivedException1_3B> JAVA_CLINIT_CHECK ()
  dassign %Reg0_R43700 0 (gcmalloc ref <$LDerivedException1_3B>)
  #INSTIDX : 11||000b:  dup
  #INSTIDX : 12||000c:  invokespecial
  callassigned &LDerivedException1_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R43700) {}
  #INSTIDX : 15||000f:  athrow
  dassign %Reg0_R510 0 (retype ref <* <$Ljava_2Flang_2FThrowable_3B>> (dread ref %Reg0_R43700))
  throw (dread ref %Reg0_R510)
  endtry
@label0   javatry { @label2 @label3 }
  #INSTIDX : 16||0010:  iload_0
  #INSTIDX : 17||0011:  iflt
  brtrue @label1 (lt i32 i32 (dread i32 %Reg4_I, constval i32 0))
  #INSTIDX : 20||0014:  new
  #intrinsiccallwithtype <$LDerivedException2_3B> JAVA_CLINIT_CHECK ()
  dassign %Reg0_R43702 0 (gcmalloc ref <$LDerivedException2_3B>)
  #INSTIDX : 23||0017:  dup
  #INSTIDX : 24||0018:  invokespecial
  callassigned &LDerivedException2_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R43702) {}
  #INSTIDX : 27||001b:  athrow
  dassign %Reg0_R510 0 (retype ref <* <$Ljava_2Flang_2FThrowable_3B>> (dread ref %Reg0_R43702))
  throw (dread ref %Reg0_R510)
  endtry
@label1   javatry { @label2 @label3 }
  #INSTIDX : 28||001c:  new
  #intrinsiccallwithtype <$LDerivedException3_3B> JAVA_CLINIT_CHECK ()
  dassign %Reg0_R43704 0 (gcmalloc ref <$LDerivedException3_3B>)
  #INSTIDX : 31||001f:  dup
  #INSTIDX : 32||0020:  invokespecial
  callassigned &LDerivedException3_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R43704) {}
  #INSTIDX : 35||0023:  athrow
  dassign %Reg0_R510 0 (retype ref <* <$Ljava_2Flang_2FThrowable_3B>> (dread ref %Reg0_R43704))
  throw (dread ref %Reg0_R510)
  endtry
@label2   javacatch { <* <$LDerivedException1_3B>> }
  dassign %Reg0_R43700 0 (regread ptr %%thrownval)
  #INSTIDX : 36||0024:  astore_2
  dassign %Reg3_R43700 0 (dread ref %Reg0_R43700)
  #INSTIDX : 37||0025:  iconst_m1
  dassign %Reg0_I 0 (constval i32 -1)
  #INSTIDX : 38||0026:  ireturn
  return (dread i32 %Reg0_I)
@label3   javacatch { <* <$LDerivedException2_3B>> }
  dassign %Reg0_R43702 0 (regread ptr %%thrownval)
  #INSTIDX : 39||0027:  astore_2
  dassign %Reg3_R43702 0 (dread ref %Reg0_R43702)
  #INSTIDX : 40||0028:  bipush
  dassign %Reg0_I 0 (constval i32 -2)
  #INSTIDX : 42||002a:  ireturn
  return (dread i32 %Reg0_I)
}
func &LExceptionTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32 {
  #funcid 48159
  var %Reg0_I i32
  var %Reg1_I i32
  var %Reg0_R43699 <* <$LBaseException_3B>>
  var %Reg2_R43699 <* <$LBaseException_3B>>

  #intrinsiccallwithtype <$LExceptionTest_3B> JAVA_CLINIT_CHECK ()
  javatry { @label4 }
  #INSTIDX : 0||0000:  bipush
  dassign %Reg0_I 0 (constval i32 10)
  #INSTIDX : 2||0002:  invokestatic
  #intrinsiccallwithtype <$LExceptionTest_3B> JAVA_CLINIT_CHECK ()
  callassigned &LExceptionTest_3B_7CTestMain_7C_28I_29I (dread i32 %Reg0_I) { dassign %Reg0_I 0 }
  #INSTIDX : 5||0005:  istore_1
  dassign %Reg1_I 0 (dread i32 %Reg0_I)
  #return (dread i32 %Reg1_I)
  #INSTIDX : 6||0006:  iconst_5
  dassign %Reg0_I 0 (constval i32 5)
  #INSTIDX : 7||0007:  invokestatic
  #intrinsiccallwithtype <$LExceptionTest_3B> JAVA_CLINIT_CHECK ()
  callassigned &LExceptionTest_3B_7CTestMain_7C_28I_29I (dread i32 %Reg0_I) { dassign %Reg0_I 0 }
  #INSTIDX : 10||000a:  istore_1
  dassign %Reg1_I 0 (dread i32 %Reg0_I)
  #return (dread i32 %Reg1_I)
  #INSTIDX : 11||000b:  bipush
  dassign %Reg0_I 0 (constval i32 -5)
  #INSTIDX : 13||000d:  invokestatic
  #intrinsiccallwithtype <$LExceptionTest_3B> JAVA_CLINIT_CHECK ()
  callassigned &LExceptionTest_3B_7CTestMain_7C_28I_29I (dread i32 %Reg0_I) { dassign %Reg0_I 0 }
  #INSTIDX : 16||0010:  istore_1
  dassign %Reg1_I 0 (dread i32 %Reg0_I)
  endtry
  #INSTIDX : 17||0011:  goto
  goto @label5
@label4   javacatch { <* <$LBaseException_3B>> }
  dassign %Reg0_R43699 0 (regread ptr %%thrownval)
  #INSTIDX : 20||0014:  astore_2
  dassign %Reg2_R43699 0 (dread ref %Reg0_R43699)
  #INSTIDX : 21||0015:  iconst_1
  dassign %Reg0_I 0 (constval i32 1)
  #INSTIDX : 22||0016:  istore_1
  dassign %Reg1_I 0 (dread i32 %Reg0_I)
@label5   #INSTIDX : 23||0017:  return
  return (dread i32 %Reg1_I)
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
