Resources, lifecycles, and structured concurrency:
A lifetime-based approach
==================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com),
[JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)
& [Radboud Univ. Nijmegen](https://sws.cs.ru.nl/Person/Guests)


Kotlin relies on scope-based resource management but lacks mechanisms to prevent leaking, guarantee lifecycle safety, and rule out conflicting actions statically. We devise a mechanism addressing these issues in a manner compatible with structured concurrency and localized capturing in general. Our model can be seen as a generalization of the Rust approach.

# Introduction

We propose an extension to the Kotlin type system and flow-sensitive typing mechanism providing static control over aliasing and resource lifecycles. Our contribution is threefold:
- a mechanism to lock references inside the receiving scope, which opens the way for
- `modal` methods, the statically checked counterpart of Java's `synchronized` methods, and
- modes (= typestates) such as `File.Open` to keep track of object lifecycles at compile time.

\vspace{1em}
**Example 1.** Well-scoped resource acquisition (writable reference locked inside)
```kotlin
var rogueWriter: File.Writable?
file.open {
  file.write("Hello!")
  rogueWriter = file    // Error: `file : File.Writable` is confined inside open@ 
}
```
\vspace{1em}
**Example 2.** Mutual exclusion of conflicting actions using modal methods
```kotlin
|\textbf{\textcolor{dgreen}{modal}}| class Buffer {
  fun append(item: Byte) { … }
  |\textbf{\textcolor{dgreen}{modal}}| fun clear() { … }
  |\textbf{\textcolor{dgreen}{using}}| fun iterate(block: (&Iterator)-> Unit)  { … }
}
```
```kotlin
buf.iterate { iterator ->
  buf.append(0xFE)  // This is ok
  buf.clear()       // Error: Modal `buf.clear()` can't be invoked while
}                   //  `buf` is borrowed by the modal `buf.iterate()`
```
\vspace{1em}
**Example 3.** Staged builders (illustrating lifecycle safety for a custom lifecycle)
```kotlin
class Html : Tag("html") |\textbf{\textcolor{dgreen}{with}}| AwaitsHead { 
  |\textbf{\textcolor{dgreen}{modal! extension}}| AwaitsHead {                                  // Html.AwaitsHead
    break continue@AwaitsBody                                    //  │
    fun head(head: |\textbf{\textcolor{dgreen}{once}}| Head.()-> Unit) = initTag(Head(), head)  //  │  head { ... }
  }                                                              //  ↓
  |\textbf{\textcolor{dgreen}{modal! extension}}| AwaitsBody  {                                 // Html.AwaitsBody
    break                                                        //  │
    fun body(body: |\textbf{\textcolor{dgreen}{once}}| Body.()-> Unit) = initTag(Body(), body)  //  │  body { ... }
  }                                                              //  ↓
}                                                                // Html
```
```kotlin
fun html(block: |\textbf{\textcolor{dgreen}{once}}| Html.AwaitsHead.()-> Unit) = Html().apply(block)
```

# Bound parameters and object-bound types

Higher-order functions `f(block: (X)-> Y): Z` typically only use their parameter function `block()` inside without ever leaking it outside. Nowadays it can be specified by the `CallsInPlace` contract, but we think this property must be an integral part of the signature so
we can know if `block` is allowed to perform non-local jumps and access local variables, etc. Besides, it greatly improves the behavioural predictability of high-order functions. We propose
the following notation:
```kotlin
fun foo(block: |\textbf{\textcolor{dgreen}{bound}}| (X)-> Y)
```

`CallsInPlace` also allows restricting invocation multiplicity, which we propose denoting as follows:
```kotlin
fun foo(block: |\textbf{\textcolor{dgreen}{once}}| (X)-> Y)   // exactly once
fun foo(block: |\textbf{\textcolor{dgreen}{once?}}| (X)-> Y)  // at most once
fun foo(block: |\textbf{\textcolor{dgreen}{once+}}| (X)-> Y)  // at least once
```

[Elsewhere](https://akuklev.github.io/kotlin/kotlin_purity.pdf) we also propose the modifier
```kotlin
fun foo(block: |\textbf{\textcolor{dgreen}{pure}}| (X)-> Y)
```
for functions that do not access anything non-pure at all, so their invocation multiplicity must play no role whatsoever. A typical example would be `sortWith(c: pure Comparator<T>)`.

There is one essential case where we need more flexibility, namely `CoroutineScope.launch`: 
```kotlin
interface CoroutineScope {
  ...
  fun launch(block: |\textbf{\textcolor{dgreen}{bound}}|(this) |\textbf{\textcolor{dgreen}{suspend}}| ()-> Unit): Job
}
```

Here, `block` is not bound inside `launch` itself but rather inside the surrounding coroutine scope.

Knowing if a parameter leaks the receiving scope is crucial not only for parameters `block : (X)-> Y` of function types. In Kotlin, all objects (that is, values of non-primitive types) are passed by-reference, so both formal and informal reasoning about program behaviour becomes nearly impossible if we don't know whether the parameters are allowed to leak or are used internally only. So let's allow using `bound` for parameters of any non-primitive types, and we'll also need to allow parametrized `bound` for return types:
```kotlin
fun foo(f: |\textbf{\textcolor{dgreen}{bound}}| File)
fun bar(f: File): |\textbf{\textcolor{dgreen}{bound}}|(f) FileOutputStream
```

By allowing `bound` in `val`s we can introduce local variables of non-primitive types: 
```kotlin
fun f() {
  val user: |\textbf{\textcolor{dgreen}{bound}}| MutableUserData
}
```

Bound parameters are so pervasive that the notation `f(x: bound OutputStream)` would bloat signatures if used for every bound parameter, so we propose an even shorter notation: `f(x: &OutputStream)` unless used with function types or parameters:
```kotlin
fun <T, R> T.use(block: |\textbf{\textcolor{dgreen}{once}}| (&T)-> R): R
fun <R> coroutineScope(block: |\textbf{\textcolor{dgreen}{once}}| &CoroutineScope.()-> R): R
```

Bound parameters are only allowed to be captured inside objects and function literals which are themselves of bound types and cannot outlive the scope the parameters are bound inside. When bound parameters are passed on as arguments, the compiler must check they are de facto^[Alowing to pass only to functions that explicitly state boundness would ruin backwards compatibility and interoperability.] bound, i.e. they don't leak from the receiving function.

Object-bound parameters are crucial for structured concurrency:
```kotlin
file.printWriter().use {
  coroutineScope {
    for (i in 1..99) launch {
      delay(Random.nextInt(0, 100))
      it.println("${i.th} asynchronous bottle of beer")
    }
  }
  it.println("No more bottles of beer!")
}
```
 
Here, we acquire a `PrintWriter`, launch 99 jobs populating it by `"${i.th} asynchronous bottle of beer"` after a random delay, and add `"No more bottles of beer!"` when they're all done.   
The function literal where `it.println(…)` is invoked is not a simple `bound` parameter, but one bound to the enclosing `coroutineScope`. The invocation is still allowed because the `coroutineScope` is itself bound inside the scope where `it` is bound.

Object-bound return types allow capturing arguments inside freshly created objects:
```kotlin
file.use { f ->
  val out = f.outputStream()
}
```

Object-binding of types must be allowed in inheritance lists as well. Let us consider the case that shows up in frameworks like JPA/Hibernate (courtesy of Tunahan Pınar), where operations are run within a transaction, which manages a temporary database session (`EntityManager`):
```kotlin
fun <R> transaction(block: |\textbf{\textcolor{dgreen}{once}}| (&EntityManager)-> R): R
```
A bug occurs when an object with lazy-loaded fields, which depends on this live session, is returned from the transaction scope. Any later attempt to access the lazy data will fail because the session has been closed, causing a `LazyInitializationException`. We still want to be able to return such an object, yet stripped of lazily loaded properties. We can do this as follows. We can have a universal class for non-lazy fields and an interface for lazy-loaded ones:
```kotlin
class BaseEntity<T>(val id: Long) { … }
```
```kotlin
interface User : DbEntity{
  val id: Long
```
```kotlin
  @OneToMany(mappedBy = User::class)
  val posts: List<Post>
}
```

`EntityManager` members that retrieve database entities would not generate their proxy objects:
```kotlin
return object : BaseEntity<User>(id), bound(this) User {
  val posts: ProxyList<Post> by em.column("posts", id)
}
```

Let us consider the following piece of code:
```kotlin
val user = DatabaseManager.transaction { em ->
    val user = em.find<User>(1L)
    println(user.posts.size) // OK!
    return user // Upcast to the nearest non-bound superclass `BaseEntity<User>` 
}
println(user.posts.size) // <- Property .posts not found!
// — what used to be a runtime exception is now being caught already by the IDE.
```
```kotlin
println(user.id)  // Still OK!
```

# Modal objects

Kotlin type system, as it stands, does not reflect the fact that object members may become unavailable after certain actions, or for the duration of certain actions:
- Closeable resources cannot be accessed after being closed;
- Closeable resources cannot be closed while being used;
- Mutable collections cannot be structurally modified while being iterated.

To enforce these constraints, we'll introduce modal methods: methods that are not allowed to be invoked while their host object is being “used by a third party”. We propose using the `break` modifier for modal methods that finalize their host object, and the `modal` modifier for methods that lock their host object for the duration of their invocation. Classes with modal methods will also be declared modal. If they have any finalizing methods, it has to be declared if finalization is mandatory (`modal!`) or optional (`modal?`):
```kotlin
|\textbf{\textcolor{dgreen}{modal?}}| class ProtectedStore<T> {
  operator fun get(index: Int): T { … }
  |\textbf{\textcolor{dgreen}{modal}}| operator fun set(index: Int, value: T) { … }
  |\textbf{\textcolor{dgreen}{break}}| fun close() { … }
}
```

Whenever pass a modal object as a bound parameter, no modal methods can be called as long as the bound reference exists:
```kotlin
val store = ProtectedStore<String>()
store[1] = "Hello"
store.use { store ->
  println(store[1])             // OK
  coroutineScope {
    launch {println(store[1])}  // Also OK
  }
  store[2] = "World"   // Forbidden! 
  store.close()        // Also forbidden!
}
store[2] = "World"   // OK! 
store.close()        // OK!
println(store[1])    // Store has been closed
```

If `M` is a modal type, we will treat passing parameters `foo(obj : M)` very differently from the case of a non-modal type: as borrowing. As opposed to the case of `bar(obj : &M)`, `foo` will be allowed to call modal methods of `obj` and even required to finalize it if `M` is a modal type with mandatory finalization. Borrowed parameters can be reborrowed to some other functions or objects (see Borrowing by Modal Objects below) or temporarily passed on as bound parameters. Borrowed parameters are not allowed to be captured at all, unless bound first.

Optionally finalizable objects must be cast manually after being borrowed and returned:
```kotlin
foo(store)
when(f) {
  is ProtectedStore -> // store was not consumed by foo
  else ->              // f was consumed by foo
}
```

There is a third way to pass a modal object as a parameter: we can upcast them to a non-modal supertype. If `T` is a non-modal supertype of `M`, `foo(x : T)` receives a usual shared reference to `T`, which cannot be used to invoke any modal or finalizing methods of `x`. References of non-modal types `x: T` should never be allowed to be cast to modal types `M`, except in atomic guarded invocations `(r as M).foo()` and `(r as? M)?.foo()`.

At-most-once and exactly-once functions can be defined in terms of modal objects:
```kotlin
|\textbf{\textcolor{dgreen}{modal!}}| fun interface ExactlyOnceFunction<X, Y> {
  break fun invoke(x: X): Y   // must be invoked exactly once
}
```
```kotlin
|\textbf{\textcolor{dgreen}{modal?}}| fun interface OnceOrLessFunction<X, Y> {
  break fun invoke(x: X): Y   // can be invoked at most once
}
```


Using modal methods, we can introduce mutable objects with the same usage policies as in Rust. This use case is so ubiquitous we want to introduce a special notation:
```kotlin
|\textbf{\textcolor{dgreen}{modal}}| data class MutableAddress(var street: String, var city: String)
// Desugars to
|\textbf{\textcolor{dgreen}{modal}}| interface MutableAddress {
  var street: String
  var city: String
  companion object {
    fun invoke(val initStreet, val initCity) = object : MutableAddress {
      override var street = initStreet
      |\textbf{\textcolor{dgreen}{modal}}| set(value) { field = value }
```
```kotlin
      override var city = initCity
      |\textbf{\textcolor{dgreen}{modal}}| set(value) { field = value }  
    }
  }
}
```

Now if we use `MutableAddress` as a type for a local `val`, it is automatically a local variable (never leaks the scope, can be garbage-collected as soon as the function returns). Mutable/read-only references in Rust exactly match the semantics of our borrowed/bound references, respectively.

One can even go further and extend the definition of normal data classes to automatically generate a modal mutable variant and a deep `copy()` method:
```kotlin
data class User(val name: String, val posts: List<Posts>)
// Desugars to
class User(val name: String, val posts: List<Post>) {
  |\textbf{\textcolor{dgreen}{modal}}| data class Mutable(var name: String, val posts: List.Mutable<Post.Mutable>)  
  fun copy(block: Mutable.()-> Unit) : User { … }
  ...
}
```

We propose introducing a new modifier keyword `using` to mark receiver (`this`) as a bound parameter. Let us illustrate the usage on the example of the buffer, which can be grown but not cleared while being iterated:
```kotlin
|\textbf{\textcolor{dgreen}{modal}}| class Buffer {
  fun append(item: Byte) { … }
  |\textbf{\textcolor{dgreen}{modal}}| fun clear() { … }
  |\textbf{\textcolor{dgreen}{using}}| fun iterate(block: (&Iterator)-> Unit)  { … }
}
```

For the duration of a `modal` method, the original reference is shadowed by a bound reference:
```kotlin
buf.iterate {
  buf.append(0xFE)  // inside, `buf` is a bound reference
  buf.clear()       // Forbidden! Bound reference cannot be used to invoke modal methods
}
```

We also propose using the `using` keyword for indentation-sparing syntax from `C#`:
```kotlin
|\textbf{\textcolor{dgreen}{using}}| file.open
|\textbf{\textcolor{dgreen}{using}}| val connection = withConnection
restOfTheBlock
// Desugars to
file.open {
  withConnection { connection ->
    restOfTheBlock
  }
}
```

# Modes

To represent objects with a complex lifecycle, we propose borrowing (pun intended) yet another mechanism from Scala, namely the extension classes, described in <https://docs.scala-lang.org/tour/self-types.html>. Kotlin-style semantics of extension classes could be easily described if inheritance by delegation were available not only for interfaces but also for classes:
```kotlin
|\textbf{\textcolor{dgreen}{extension}}| Parent.Mode(…) { … } -->  class Mode(p: Parent, …) : Parent by p { … }
```

Extensions can be declared inside the class they extend, in which case the `Parent.` prefix is omitted. They can also be nested. Extensions are used to refine objects (that is, add and override members) after they have been constructed. Extensions can be constructed using `with`-clauses: `Parent(…) with Mode`. We'll be using extensions to introduce method modifiers `continue@Mode`, `break@Mode`^[The parallels to ordinary `break` and `continue` become evident when introducing type-safe actor model.], and `using@Mode`. It will be crucial to allow overriding modal methods by non-modal ones in extensions.

Methods with `continue@Mode` modifier substitute the host reference by its `Mode`-extension. Delegation by omission is allowed as well:
```kotlin
|\textbf{\textcolor{dgreen}{modal!}}| fun interface AtLeastOnceFunction<X, Y> {   // Shorthand: once+ (X)-> Y
  continue@Unlocked fun invoke(x : X) : Y   // must be invoked at least once
  |\textbf{\textcolor{dgreen}{extension}}| Unlocked : Function<X, Y> {
    fun invoke(x : X) : Y
  }
}
```

Methods with `using@Mode` temporarily substitute the host reference by a bound reference to the `Mode`-extension:
```kotlin
class File {
  |\textbf{\textcolor{dgreen}{using}}|@Open fun <R> open(block: |\textbf{\textcolor{dgreen}{once}}| ()-> R)
}
```

Since extensions can be nested, we also need qualified `break@Mode`. Unqualified `break` finalizes the outermost modal parent.

Both `break` and `using` can be combined with `continue@Mode` allowing arbitrary typelevel state automata. For an example let us consider an HTML builder.^[If you are unfamiliar with this example, please consult <https://kotlinlang.org/docs/type-safe-builders.html>] It provides an embedded type-safe DSL for constructing HTML:
```kotlin
val h = html {
  head { ... }
  body { ... }
}
```
To require exactly one head and exactly one body after it, we'll need a staged builder:
```kotlin
class Html : Tag("html") |\textbf{\textcolor{dgreen}{with}}| AwaitsHead { 
  |\textbf{\textcolor{dgreen}{modal! extension}}| AwaitsHead {                                  // Html.AwaitsHead
    break continue@AwaitsBody                                    //  │
    fun head(head : |\textbf{\textcolor{dgreen}{once}}| Head.()-> Unit) = initTag(Head(), head) //  │  head { ... }
  }                                                              //  ↓
  |\textbf{\textcolor{dgreen}{modal! extension}}| AwaitsBody  {                                 // Html.AwaitsBody
    break                                                        //  │
    fun body(body : |\textbf{\textcolor{dgreen}{once}}| Body.()-> Unit) = initTag(Body(), body) //  │  body { ... }
  }                                                              //  ↓
}                                                                // Html
```

Here we declare a staged class `Html` that extends `Tag("html")` and has two additional modes `AwaitsHead` and `AwaitsBody` with methods `head()` and `body()` respectively. Both methods are finalizing methods, but `head()` additionally continues to the `AwaitsBody`, while `body()` leaves the bare non-modal `Html` object which provides members inherited from `Tag`. The initial mode of this object is specified using a `with`-clause borrowed from Scala.

Finally, we want to mention that non-abstract `class Parent with Mode` is allowed to have abstract members as long as they are implemented by `Mode`. Also note that if the extension `Mode` has constructor arguments and/or abstract methods, `continue@Mode` functions, `modal@Mode` and the constructor of `class Parent with Mode` must contain an `init Mode(args) {methods}` block providing those arguments and/or methods. `modal continue@NextMode` functions initialize `NextMode` in their `finally { … }` block. This is also where `using@Mode` functions have/can to finalize `Mode` if it is `modal!` or `modal?` respectively.

# Polyphonic structured concurrency

Presently, resources have to be initialized and finalized sequentially even if they are independent:
```kotlin
withA { a -> 
  withB { b ->
    ...
  }
}
```
In many cases, parallel initialization and finalization would be beneficial:
```kotlin
join(withA, withB) { (a, b) ->
  ...
}
```

A structurally concurrent implementation of `join` requires a polyphonic definition, that is a simultaneous definition of multiple single-shot suspend functions with a common body:
```kotlin
|\textbf{\textcolor{dgreen}{join}}| fun f(x: Int) & fun g(y: Int) {
   return@f (x + y)
   return@g (x - y)
}
launch {
  delay(Random.nextInt(0, 100))
  println(f(5))
}
launch {
  delay(Random.nextInt(0, 100))
  println(g(3))
}
```

Here is how we can implement parallel resource initialization and finalization:
```kotlin
suspend fun <R> join(withA: (|\textbf{\textcolor{dgreen}{once}}| (A)-> Unit)-> Unit,
                     withB: (|\textbf{\textcolor{dgreen}{once}}| (B)-> Unit)-> Unit,
                     block: |\textbf{\textcolor{dgreen}{once}}| (A, B)-> R): R {             
  |\textbf{\textcolor{dgreen}{join}}| fun f(a: A) & g(b: B) & r(): R {
    return@r block(a, b)
  }
  coroutineScope {
    launch { withA(::f) }
    launch { withB(::g) }
    return r()  
  }
}
```

We can also allow polyphonic method definitions in multi-modal objects, e.g.
```kotlin
class Promise<T> |\textbf{\textcolor{dgreen}{with}}| Awaiting {
```
```kotlin
  abstract suspend fun await(): T
```
```kotlin
  |\textbf{\textcolor{dgreen}{extension}}| Completed(val result: T) {
    override fun await() = result
  }
  |\textbf{\textcolor{dgreen}{modal? extension}}| Awaiting {
    |\textbf{\textcolor{dgreen}{join}}| |\textbf{\textcolor{dgreen}{break continue}}|@Completed fun complete(x : T)
       & override fun await(): T {
      init Completed(x)
      return@await x
    }
  }
```

Polyphonic definitions tightly intertwine type-checking and control-flow analysis, but it is the only known way to express arbitrary initialization, finalization, communication, and synchronization patterns in a structurally concurrent way.

# Conclusion

We have outlined a coherent system of mechanisms for lifecycle-aware resource handling that provides comprehensive correctness guarantees and makes concurrent interactive programming amenable to formal reasoning\footnote{See \href{https://arxiv.org/abs/2207.04034}{“Flux: Liquid Types for Rust” by N Lehmann, A Geller, N Vazou, R Jhala}}. Our proposal has to be evaluated by developing a library of concurrent mutable collections and heaps^[Heaps with various transactional operators, heap-native structures, ghost variables, and conflict-free replicated data types in addition to pure ones, provide implementations for arbitrary flavours of separation logic.] enabling fine-grained concurrent separation logic.
