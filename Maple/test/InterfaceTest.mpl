type $LBase_3B <class <$Ljava_2Flang_2FObject_3B> {
  @a i32,
  &LBase_3B_7C_3Cinit_3E_7C_28_29V constructor (<* <$LBase_3B>>) void,
  &LBase_3B_7Cfoo_7C_28_29I public virtual (<* <$LBase_3B>>) i32,
  &LBase_3B_7Cbar_7C_28I_29I private virtual (<* <$LBase_3B>>,i32) i32,
  $LInter_3B}>
type $LB_3B <class <$Ljava_2Flang_2FObject_3B> {
  &LB_3B_7C_3Cinit_3E_7C_28_29V constructor (<* <$LB_3B>>) void}>
type $LDerived_3B <class <$LBase_3B> {
  @a i32,
  &LDerived_3B_7C_3Cinit_3E_7C_28_29V constructor (<* <$LDerived_3B>>) void,
  &LDerived_3B_7Cfoo_7C_28_29I public virtual (<* <$LDerived_3B>>) i32,
  &LDerived_3B_7Cbar_7C_28I_29I private virtual (<* <$LDerived_3B>>,i32) i32}>
type $LInter2_3B <interface  {}>
type $LInter_3B <interface  {
  #^LInter_3B_7Ca i32 final public static,
  &LInter_3B_7Cfoo_7C_28_29I public virtual abstract (<* <$LInter_3B>>) i32}>
type $LInterfaceTest_241A_3B <class <$Ljava_2Flang_2FObject_3B> {
  @x i32 private,
  &LInterfaceTest_241A_3B_7C_3Cinit_3E_7C_28_29V constructor (<* <$LInterfaceTest_241A_3B>>) void,
  &LInterfaceTest_241A_3B_7Csetx_7C_28I_29V public virtual (<* <$LInterfaceTest_241A_3B>>,i32) void,
  &LInterfaceTest_241A_3B_7Caccess_24000_7C_28LInterfaceTest_241A_3B_29I static (<* <$LInterfaceTest_241A_3B>>) i32}>
type $LInterfaceTest_3B <class <$Ljava_2Flang_2FObject_3B> {
  &LInterfaceTest_3B_7C_3Cinit_3E_7C_28_29V public constructor (<* <$LInterfaceTest_3B>>) void,
  &LInterfaceTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32}>
entryfunc &LInterfaceTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V
javaclass $LBase_3B <$LBase_3B>
javaclass $LB_3B <$LB_3B>
javaclass $LDerived_3B <$LDerived_3B>
javainterface $LInter2_3B <$LInter2_3B> abstract
javainterface $LInter_3B <$LInter_3B> abstract
javaclass $LInterfaceTest_241A_3B <$LInterfaceTest_241A_3B>
javaclass $LInterfaceTest_3B <$LInterfaceTest_3B> public
func &LBase_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LBase_3B>>) void
func &LBase_3B_7Cfoo_7C_28_29I public virtual (var %_this <* <$LBase_3B>>) i32
func &LBase_3B_7Cbar_7C_28I_29I private virtual (var %_this <* <$LBase_3B>>, var %Reg3_I i32) i32
func &LB_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LB_3B>>) void
func &LDerived_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LDerived_3B>>) void
func &LDerived_3B_7Cfoo_7C_28_29I public virtual (var %_this <* <$LDerived_3B>>) i32
func &LDerived_3B_7Cbar_7C_28I_29I private virtual (var %_this <* <$LDerived_3B>>, var %Reg2_I i32) i32
func &LInter_3B_7Cfoo_7C_28_29I public virtual abstract (var %_this <* <$LInter_3B>>) i32
func &LInterfaceTest_241A_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LInterfaceTest_241A_3B>>) void
func &LInterfaceTest_241A_3B_7Csetx_7C_28I_29V public virtual (var %_this <* <$LInterfaceTest_241A_3B>>, var %Reg3_I i32) void
func &LInterfaceTest_241A_3B_7Caccess_24000_7C_28LInterfaceTest_241A_3B_29I static (var %Reg1_R43712 <* <$LInterfaceTest_241A_3B>>) i32
func &LInterfaceTest_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LInterfaceTest_3B>>) void
func &LInterfaceTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32
var $LInter_3B_7Ca i32
func &LDerived_3B_7Cfoo_7C_28_29I public virtual (var %_this <* <$LDerived_3B>>) i32
#var $Ljava_2Flang_2FSystem_3B_7Cout extern <* <$Ljava_2Fio_2FPrintStream_3B>> final public static
#var $__cinf_Ljava_2Flang_2FString_3B extern <$__class_meta__>
#func &MCC_GetOrInsertLiteral () <* <$Ljava_2Flang_2FString_3B>>
func &LBase_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LBase_3B>>) void {
  #funcid 48153
  var %Reg3_R43701 <* <$LBase_3B>>
  var %Reg3_R57 <* <$Ljava_2Flang_2FObject_3B>>
  var %Reg0_I i32

  dassign %Reg3_R43701 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg3_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg3_R43701))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg3_R57) {}
  #INSTIDX : 4||0004:  aload_0
  #INSTIDX : 5||0005:  aload_0
  #INSTIDX : 6||0006:  iconst_5
  dassign %Reg0_I 0 (constval i32 5)
  #INSTIDX : 7||0007:  invokespecial
  callassigned &LBase_3B_7Cbar_7C_28I_29I (dread ref %Reg3_R43701, dread i32 %Reg0_I) { dassign %Reg0_I 0 }
  #INSTIDX : 10||000a:  putfield
  iassign <* <$LBase_3B>> 4 (dread ref %Reg3_R43701, dread i32 %Reg0_I)
  #INSTIDX : 13||000d:  return
  return ()
}
func &LBase_3B_7Cfoo_7C_28_29I public virtual (var %_this <* <$LBase_3B>>) i32 {
  #funcid 48154
  var %Reg1_R43701 <* <$LBase_3B>>
  var %Reg0_I i32

  dassign %Reg1_R43701 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  getfield
  dassign %Reg0_I 0 (iread i32 <* <$LBase_3B>> 4 (dread ref %Reg1_R43701))
  #INSTIDX : 4||0004:  ireturn
  return (dread i32 %Reg0_I)
}
func &LBase_3B_7Cbar_7C_28I_29I private virtual (var %_this <* <$LBase_3B>>, var %Reg3_I i32) i32 {
  #funcid 48155
  var %Reg2_R43701 <* <$LBase_3B>>
  var %Reg0_I i32

  dassign %Reg2_R43701 0 (dread ref %_this)
  #INSTIDX : 0||0000:  bipush
  dassign %Reg0_I 0 (constval i32 10)
  #INSTIDX : 2||0002:  iload_1
  #INSTIDX : 3||0003:  idiv
  dassign %Reg0_I 0 (div i32 (dread i32 %Reg0_I, dread i32 %Reg3_I))
  #INSTIDX : 4||0004:  ireturn
  return (dread i32 %Reg0_I)
}
func &LB_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LB_3B>>) void {
  #funcid 48156
  var %Reg1_R43705 <* <$LB_3B>>
  var %Reg1_R57 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg1_R43705 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg1_R43705))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R57) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LDerived_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LDerived_3B>>) void {
  #funcid 48157
  var %Reg2_R43707 <* <$LDerived_3B>>
  var %Reg2_R43701 <* <$LBase_3B>>
  var %Reg0_I i32

  dassign %Reg2_R43707 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg2_R43701 0 (retype ref <* <$LBase_3B>> (dread ref %Reg2_R43707))
  callassigned &LBase_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg2_R43701) {}
  #INSTIDX : 4||0004:  aload_0
  #INSTIDX : 5||0005:  bipush
  dassign %Reg0_I 0 (constval i32 6)
  #INSTIDX : 7||0007:  putfield
  iassign <* <$LDerived_3B>> 6 (dread ref %Reg2_R43707, dread i32 %Reg0_I)
  #INSTIDX : 10||000a:  return
  return ()
}
func &LDerived_3B_7Cfoo_7C_28_29I public virtual (var %_this <* <$LDerived_3B>>) i32 {
  #funcid 48158
  var %Reg3_R43707 <* <$LDerived_3B>>
  var %Reg3_R43701 <* <$LBase_3B>>
  var %Reg0_I i32
  var %Reg2_I i32
  var %Reg1_I i32

  dassign %Reg3_R43707 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg3_R43701 0 (retype ref <* <$LBase_3B>> (dread ref %Reg3_R43707))
  callassigned &LBase_3B_7Cfoo_7C_28_29I (dread ref %Reg3_R43701) { dassign %Reg0_I 0 }
  #INSTIDX : 4||0004:  istore_1
  dassign %Reg2_I 0 (dread i32 %Reg0_I)
  #INSTIDX : 5||0005:  aload_0
  #INSTIDX : 6||0006:  getfield
  dassign %Reg0_I 0 (iread i32 <* <$LDerived_3B>> 6 (dread ref %Reg3_R43707))
  #INSTIDX : 9||0009:  aload_0
  #INSTIDX : 10||000a:  getfield
  dassign %Reg3_R43701 0 (retype ref <* <$LBase_3B>> (dread ref %Reg3_R43707))
  dassign %Reg1_I 0 (iread i32 <* <$LBase_3B>> 4 (dread ref %Reg3_R43701))
  #INSTIDX : 13||000d:  iadd
  dassign %Reg0_I 0 (add i32 (dread i32 %Reg0_I, dread i32 %Reg1_I))
  #INSTIDX : 14||000e:  istore_1
  dassign %Reg2_I 0 (dread i32 %Reg0_I)
  #INSTIDX : 15||000f:  iload_1
  #INSTIDX : 16||0010:  ireturn
  return (dread i32 %Reg2_I)
}
func &LDerived_3B_7Cbar_7C_28I_29I private virtual (var %_this <* <$LDerived_3B>>, var %Reg2_I i32) i32 {
  #funcid 48158
  var %Reg1_R43707 <* <$LDerived_3B>>
  var %Reg0_I i32

  dassign %Reg1_R43707 0 (dread ref %_this)
  #INSTIDX : 0||0000:  iconst_2
  dassign %Reg0_I 0 (constval i32 2)
  #INSTIDX : 1||0001:  ireturn
  return (dread i32 %Reg0_I)
}
func &LInter_3B_7Cfoo_7C_28_29I public virtual abstract (var %_this <* <$LInter_3B>>) i32
func &LInterfaceTest_241A_3B_7C_3Cinit_3E_7C_28_29V constructor (var %_this <* <$LInterfaceTest_241A_3B>>) void {
  #funcid 48160
  var %Reg1_R43712 <* <$LInterfaceTest_241A_3B>>
  var %Reg1_R57 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg1_R43712 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg1_R43712))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R57) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LInterfaceTest_241A_3B_7Csetx_7C_28I_29V public virtual (var %_this <* <$LInterfaceTest_241A_3B>>, var %Reg3_I i32) void {
  #funcid 48161
  var %Reg2_R43712 <* <$LInterfaceTest_241A_3B>>

  dassign %Reg2_R43712 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  iload_1
  #INSTIDX : 2||0002:  putfield
  iassign <* <$LInterfaceTest_241A_3B>> 4 (dread ref %Reg2_R43712, dread i32 %Reg3_I)
  #INSTIDX : 5||0005:  return
  return ()
}
func &LInterfaceTest_241A_3B_7Caccess_24000_7C_28LInterfaceTest_241A_3B_29I static (var %Reg1_R43712 <* <$LInterfaceTest_241A_3B>>) i32 {
  #funcid 48162
  var %Reg0_I i32

  #intrinsiccallwithtype <$LInterfaceTest_241A_3B> JAVA_CLINIT_CHECK ()
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  getfield
  dassign %Reg0_I 0 (iread i32 <* <$LInterfaceTest_241A_3B>> 4 (dread ref %Reg1_R43712))
  #INSTIDX : 4||0004:  ireturn
  return (dread i32 %Reg0_I)
}
func &LInterfaceTest_3B_7C_3Cinit_3E_7C_28_29V public constructor (var %_this <* <$LInterfaceTest_3B>>) void {
  #funcid 48163
  var %Reg1_R43716 <* <$LInterfaceTest_3B>>
  var %Reg1_R57 <* <$Ljava_2Flang_2FObject_3B>>

  dassign %Reg1_R43716 0 (dread ref %_this)
  #INSTIDX : 0||0000:  aload_0
  #INSTIDX : 1||0001:  invokespecial
  dassign %Reg1_R57 0 (retype ref <* <$Ljava_2Flang_2FObject_3B>> (dread ref %Reg1_R43716))
  callassigned &Ljava_2Flang_2FObject_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg1_R57) {}
  #INSTIDX : 4||0004:  return
  return ()
}
func &LInterfaceTest_3B_7Cmain_7C_28ALjava_2Flang_2FString_3B_29V public static () i32 {
  #funcid 48164
  var %Reg0_R43707 <* <$LDerived_3B>>
  var %Reg2_R43707 <* <$LDerived_3B>>
  var %Reg0_I i32
  var %Reg3_I i32
  #var %Reg0_R562 <* <$Ljava_2Fio_2FPrintStream_3B>>
  var %Reg1_I i32
  var %Reg4_R43707 <* <$LDerived_3B>>
  var %Reg4_R43701 <* <$LBase_3B>>
  var %Reg5_R43707 <* <$LDerived_3B>>
  var %Reg5_R43710 <* <$LInter_3B>>
  var %Reg6_I i32
  var %Reg0_R43712 <* <$LInterfaceTest_241A_3B>>
  var %Reg7_R43712 <* <$LInterfaceTest_241A_3B>>

  #intrinsiccallwithtype <$LInterfaceTest_3B> JAVA_CLINIT_CHECK ()
  #INSTIDX : 0||0000:  new
  #intrinsiccallwithtype <$LDerived_3B> JAVA_CLINIT_CHECK ()
  dassign %Reg0_R43707 0 (gcmalloc ref <$LDerived_3B>)
  #INSTIDX : 3||0003:  dup
  #INSTIDX : 4||0004:  invokespecial
  callassigned &LDerived_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R43707) {}
  #INSTIDX : 7||0007:  astore_1
  dassign %Reg2_R43707 0 (dread ref %Reg0_R43707)
  #INSTIDX : 8||0008:  aload_1
  #INSTIDX : 9||0009:  invokevirtual
  virtualcallassigned &LDerived_3B_7Cfoo_7C_28_29I (dread ref %Reg2_R43707) { dassign %Reg0_I 0 }
  #INSTIDX : 12||000c:  istore_2
  dassign %Reg3_I 0 (dread i32 %Reg0_I)
  #return (dread i32 %Reg3_I)
  #INSTIDX : 13||000d:  getstatic
  #intrinsiccallwithtype <$Ljava_2Flang_2FSystem_3B> JAVA_CLINIT_CHECK ()
  #dassign %Reg0_R562 0 (dread ref $Ljava_2Flang_2FSystem_3B_7Cout)
  #INSTIDX : 16||0010:  aload_1
  #INSTIDX : 17||0011:  getfield
  dassign %Reg1_I 0 (iread i32 <* <$LDerived_3B>> 6 (dread ref %Reg2_R43707))
  #return (dread i32 %Reg1_I)
  #INSTIDX : 20||0014:  invokevirtual
  #virtualcallassigned &Ljava_2Fio_2FPrintStream_3B_7Cprintln_7C_28I_29V (dread ref %Reg0_R562, dread i32 %Reg1_I) {}
  #INSTIDX : 23||0017:  new
  #intrinsiccallwithtype <$LDerived_3B> JAVA_CLINIT_CHECK ()
  dassign %Reg0_R43707 0 (gcmalloc ref <$LDerived_3B>)
  #INSTIDX : 26||001a:  dup
  #INSTIDX : 27||001b:  invokespecial
  callassigned &LDerived_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R43707) {}
  #INSTIDX : 30||001e:  astore_3
  dassign %Reg4_R43707 0 (dread ref %Reg0_R43707)
  #INSTIDX : 31||001f:  getstatic
  #intrinsiccallwithtype <$Ljava_2Flang_2FSystem_3B> JAVA_CLINIT_CHECK ()
  #dassign %Reg0_R562 0 (dread ref $Ljava_2Flang_2FSystem_3B_7Cout)
  #INSTIDX : 34||0022:  aload_3
  #INSTIDX : 35||0023:  getfield
  dassign %Reg4_R43701 0 (retype ref <* <$LBase_3B>> (dread ref %Reg4_R43707))
  dassign %Reg1_I 0 (iread i32 <* <$LBase_3B>> 4 (dread ref %Reg4_R43701))
  #return (dread i32 %Reg1_I)
  #INSTIDX : 38||0026:  invokevirtual
  #virtualcallassigned &Ljava_2Fio_2FPrintStream_3B_7Cprintln_7C_28I_29V (dread ref %Reg0_R562, dread i32 %Reg1_I) {}
  #INSTIDX : 41||0029:  aload_3
  #INSTIDX : 42||002a:  invokevirtual
  dassign %Reg4_R43701 0 (retype ref <* <$LBase_3B>> (dread ref %Reg4_R43707))
  virtualcallassigned &LBase_3B_7Cfoo_7C_28_29I (dread ref %Reg4_R43701) { dassign %Reg0_I 0 }
  #INSTIDX : 45||002d:  istore_2
  dassign %Reg3_I 0 (dread i32 %Reg0_I)
  #return (dread i32 %Reg3_I)
  #INSTIDX : 46||002e:  new
  #intrinsiccallwithtype <$LDerived_3B> JAVA_CLINIT_CHECK ()
  dassign %Reg0_R43707 0 (gcmalloc ref <$LDerived_3B>)
  #INSTIDX : 49||0031:  dup
  #INSTIDX : 50||0032:  invokespecial
  callassigned &LDerived_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R43707) {}
  #INSTIDX : 53||0035:  astore 4
  dassign %Reg5_R43707 0 (dread ref %Reg0_R43707)
  #INSTIDX : 55||0037:  aload 4
  #INSTIDX : 57||0039:  invokeinterface
  dassign %Reg5_R43710 0 (retype ref <* <$LInter_3B>> (dread ref %Reg5_R43707))
  interfacecallassigned &LInter_3B_7Cfoo_7C_28_29I (dread ref %Reg5_R43710) { dassign %Reg0_I 0 }
  #INSTIDX : 62||003e:  istore_2
  dassign %Reg3_I 0 (dread i32 %Reg0_I)
  #return (dread i32 %Reg3_I)
  #INSTIDX : 63||003f:  bipush
  dassign %Reg0_I 0 (constval i32 100)
  #INSTIDX : 65||0041:  istore 5
  dassign %Reg6_I 0 (dread i32 %Reg0_I)
  #INSTIDX : 67||0043:  new
  #intrinsiccallwithtype <$LInterfaceTest_241A_3B> JAVA_CLINIT_CHECK ()
  dassign %Reg0_R43712 0 (gcmalloc ref <$LInterfaceTest_241A_3B>)
  #INSTIDX : 70||0046:  dup
  #INSTIDX : 71||0047:  invokespecial
  callassigned &LInterfaceTest_241A_3B_7C_3Cinit_3E_7C_28_29V (dread ref %Reg0_R43712) {}
  #INSTIDX : 74||004a:  astore 6
  dassign %Reg7_R43712 0 (dread ref %Reg0_R43712)
  #INSTIDX : 76||004c:  aload 6
  #INSTIDX : 78||004e:  bipush
  dassign %Reg0_I 0 (constval i32 100)
  #INSTIDX : 80||0050:  invokevirtual
  virtualcallassigned &LInterfaceTest_241A_3B_7Csetx_7C_28I_29V (dread ref %Reg7_R43712, dread i32 %Reg0_I) {}
  #INSTIDX : 83||0053:  aload 6
  #INSTIDX : 85||0055:  invokestatic
  #intrinsiccallwithtype <$LInterfaceTest_241A_3B> JAVA_CLINIT_CHECK ()
  callassigned &LInterfaceTest_241A_3B_7Caccess_24000_7C_28LInterfaceTest_241A_3B_29I (dread ref %Reg7_R43712) { dassign %Reg0_I 0 }
  #INSTIDX : 88||0058:  istore_2
  dassign %Reg3_I 0 (dread i32 %Reg0_I)
  #return (dread i32 %Reg3_I)
  #INSTIDX : 89||0059:  return
  return (constval i32 1)
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
