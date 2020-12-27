type $Ljava_2Flang_2FObject_3B <class {
  @shadow_24__klass__ i32 private,
  @shadow_24__monitor__ i32 private,
  &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V public constructor (i32) void}>
type $LFibonacci_3B <class <$Ljava_2Flang_2FObject_3B> {
  &LFibonacci_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LFibonacci_3B>>) void,
  &LFibonacci_3B_7Cfib_7C_28I_29I public static (i32) i32,
  &LFibonacci_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32}>
entryfunc &LFibonacci_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V
javaclass $LFibonacci_3B <$LFibonacci_3B> public
func &LFibonacci_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LFibonacci_3B>>) void
func &LFibonacci_3B_7Cfib_7C_28I_29I public static (var %Reg6_I i32) i32
func &LFibonacci_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32
#var $__cinf_Ljava_2Flang_2FString_3B extern <$__class_meta__>
#func &MCC_GetOrInsertLiteral () <* <$Ljava_2Flang_2FString_3B>>
func &LFibonacci_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LFibonacci_3B>>) void {
  #funcid 48153
  var %Reg1_R43694 <* <$LFibonacci_3B>>
  var %Reg1_R57 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg1_R43694 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg1_R43694))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R57) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LFibonacci_3B_7Cfib_7C_28I_29I public static (var %Reg6_I i32) i32 {
  #funcid 48154
  var %Reg0_I i32
  var %Reg2_I i32
  var %Reg3_I i32
  var %Reg4_I i32
  var %Reg5_I i32
  var %Reg1_I i32

  #intrinsiccallwithtype <$LFibonacci_3B> JAVA_CLINIT_CHECK ()
  #INSTIDX : 0||0000:  iload_0
  #INSTIDX : 1||0001:  ifne
  brtrue @label0 (ne i32 i32 (dread i32 %Reg6_I, constval i32 0))
  #INSTIDX : 4||0004:  iconst_0
  dassign %Reg0_I 0 (constval i32 0)
  #INSTIDX : 5||0005:  ireturn
  return (dread i32 %Reg0_I)
@label0   #INSTIDX : 6||0006:  iconst_1
  dassign %Reg0_I 0 (constval i32 1)
  #INSTIDX : 7||0007:  istore_1
  dassign %Reg2_I 0 (dread i32 %Reg0_I)
  #INSTIDX : 8||0008:  iconst_0
  dassign %Reg0_I 0 (constval i32 0)
  #INSTIDX : 9||0009:  istore_2
  dassign %Reg3_I 0 (dread i32 %Reg0_I)
  #INSTIDX : 10||000a:  iconst_2
  dassign %Reg0_I 0 (constval i32 2)
  #INSTIDX : 11||000b:  istore_3
  dassign %Reg4_I 0 (dread i32 %Reg0_I)
@label1   #INSTIDX : 12||000c:  iload_3
  #INSTIDX : 13||000d:  iload_0
  #INSTIDX : 14||000e:  if_icmpgt
  brtrue @label2 (gt i32 i32 (dread i32 %Reg4_I, dread i32 %Reg6_I))
  #INSTIDX : 17||0011:  iload_1
  #INSTIDX : 18||0012:  istore 4
  dassign %Reg5_I 0 (dread i32 %Reg2_I)
  #INSTIDX : 20||0014:  iload_1
  #INSTIDX : 21||0015:  iload_2
  #INSTIDX : 22||0016:  iadd
  dassign %Reg0_I 0 (add i32 (dread i32 %Reg2_I, dread i32 %Reg3_I))
  #INSTIDX : 23||0017:  ldc
  dassign %Reg1_I 0 (constval i32 0x3b9aca07)
  #INSTIDX : 25||0019:  irem
  dassign %Reg0_I 0 (rem i32 (dread i32 %Reg0_I, dread i32 %Reg1_I))
  #INSTIDX : 26||001a:  istore_1
  dassign %Reg2_I 0 (dread i32 %Reg0_I)
  #INSTIDX : 27||001b:  iload 4
  #INSTIDX : 29||001d:  istore_2
  dassign %Reg3_I 0 (dread i32 %Reg5_I)
  #INSTIDX : 30||001e:  iinc
  dassign %Reg4_I 0 (add i32 (dread i32 %Reg4_I, constval i32 1))
  #INSTIDX : 33||0021:  goto
  goto @label1
@label2   #INSTIDX : 36||0024:  iload_1
  #INSTIDX : 37||0025:  ireturn
  return (dread i32 %Reg2_I)
}
func &LFibonacci_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32 {
  #funcid 48155
  var %Reg0_I i32
  var %Reg1_I i32

  #intrinsiccallwithtype <$LFibonacci_3B> JAVA_CLINIT_CHECK ()
  #INSTIDX : 0||0000:  ldc
  dassign %Reg0_I 0 (constval i32 10)
  #INSTIDX : 2||0002:  invokestatic
  #intrinsiccallwithtype <$LFibonacci_3B> JAVA_CLINIT_CHECK ()
  callassigned &LFibonacci_3B_7Cfib_7C_28I_29I (dread i32 %Reg0_I) { dassign %Reg0_I 0 }
  #INSTIDX : 5||0005:  istore_1
  dassign %Reg1_I 0 (dread i32 %Reg0_I)
  #INSTIDX : 6||0006:  return
  return (dread i32 %Reg1_I)
}
func &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$Ljava_2Flang_2FObject_3B>>) void {
  var %Reg0_R5147 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg0_R5147 0 (dread ref %_this)
  return ()
}
