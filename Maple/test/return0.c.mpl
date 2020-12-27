entryfunc &main
entryfunc &main
type $t <class {@x i32 public align(16), &foo abstract public () i32}>
javaclass $t <$t> public
#var $x i32 align(16)
func &main public () i32
func &main public () i32 {
  var %retvar_2 <[1] i32> align(16)
  #virtualcallassigned &t_foo() {}
  return (constval i32 0)
}
