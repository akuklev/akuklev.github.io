Pending objects, Inplace objects
================================

As many other languages, Kotlin employs RAII pattern to deal with resources, thus some objects may hold resources or block threads and have to be finalized. The first step to ensure correctness dealing with such objects, is to mark them by inheriting from `Pending` interface and mark the `@Finalizing` members by the respective annotation:
```kotlin
class SomeResource : Pending {
  ...
  @Finalizing fun release() {...}
}

abstract class Continuation<T> : Pending {
  @Finalizing abstract fun invoke(value : T)
}
```

When we pass such objects into functions, we can either require them to finalize the objects or forbid to finalize them:
```
fun foo(@pending x : T)   // foo MUST finalize `x`
fun bar(@borrow  x : T)   // foo is not allowed to finalize `x`
```

A pending objects cannot be mentioned after it was finalized or passed as a `@pending` argument. Functions that create or obtain a pending objects, can only pass it around as pending or borrowed arguments, futhermore each possible execution path must either finalize the object or passe it as a pending argument.

However, this requirements are not sufficient to ensure correctness because a reference to a pending or borrowed object could be captured as an element in some list, inside of some field some object, or as a variable inside a closure which could be run as a separate job. We have to ensure that these jobs are finished and these objects either finalized or inaccessible before we finalize the object.

Structured accessibility
------------------------

In Kotlin, we can define inner classes inside classes and functions/coroutines. Unless cast into a non-inner parent type such as `Any`, values of those types cannot be exposed beyond the scope where their host objects are available. If we also allow abstract inner type members in interfaces and abstract classes as in Scala, we can use these to ensure that `@borrow`'ed objects are never exposed beyond the scope they were borrowed into by imposing the following to restrictions:
- `@borrow`'ed objects are only allowed to be captured inside objects of inner types defined inside the class/function/coroutine or inner types of objects created inside this class/function/coroutine.
- The non-inner parent types of those types must provide no access to captured objects. As a simple-to-check overapproximation we might allow only `Any`.

The first restruction prevents to capture `@borrow`'ed objects inside generic containers such as `List<T>`, while the second restriction means we cannot capture `@borrow`'ed inside closures `f : (X)-> Y`, because their non-inner parent type provides the `invoke` method which has access to captured `@borrow`'ed objects. To address both restrictions we propose automatically generating “internalized” versions `this.List<T>` and `this.((X)-> Y)` of all types on demand.



Inplace objects
---------------

Often it is desirable to pass an object without allowing to capture or expose it, so let's introduce the following annotation:
```kotlin
fun foo(@inplace x : X)     // `x` can be only used inside `foo` while `foo` is executed,
                            // `x` cannot be captured or passed as non-inplace argument
```

With this annotation we can control reference uniqueness. Let us introduce the following annotation: 
```kotlin
fun bar(@dedicated x : X)      // `x` is required to be a unique reference to the object it refers to
@dedicated fun baz(...) : Y    // return value is guaranteed to be a unique reference
```

If `x` was created locally, obtained as a `dedicated` argument or a `dedicated` return value, and had not been not captured nor passed outside (except as an `@inplace`-argument), we can be sure it is a unique reference and therefore pass it as `dedicated` argument or return as a `dedicated` return value.

Let us also introduce the interface `Inplace` to mark classes and interfaces of objects not intended to be captured or exposed, for instance the contexts for type-safe builders. A variable of an inplace type can be used only inplace unless cast to a parent type that does not yet inherit from `Inplace`, e.g. `Any`. A variable can be permanently cast into an inplace type only if it is `@dedicated`, otherwise it can be cast for a single method invocation only `(x as T).someMethodOfT()`.

With inplace types, we can introduce type-level state machines. For instance, we can make a type-safe builder for HTML that requires exactly one head and exactly one body after it:
```kotlin
class HTML @GotoState<HtmlAwaitingHead> constructor() {} : TagWithText("html") {}

interface HtmlAwaitingHead : HTML, Inplace {
  @GotoState<HtmlAwaitingBody>
  fun head(f : Head.()-> Unit) = initTag(Head(), init)
}

interface HtmlAwaitingBody : HTML, Inplace {
  @Finalizing
  fun body(f : Body.()-> Unit) = initTag(Body(), init)
}

fun html(init : (@dedicated HtmlAwaitingHead).() -> Unit) : HTML {
    val html = HTML()
    html.init()
    return html
}

...

  html {
    head { ... }
    body { ... }
  }
```



------------------







Let us introduce several annotations to provide additional static guarantees for correct usage of resources:
```
inline fun <T : Discardable?, R> T.use(@once block: (@inplace T) -> R) : R

inline fun <T : Discardable?, R> with(ressource : T, @once block: (@inplace T).() -> R) : R
```


Kotlin relies on closures to deal with ressources:
```kotlin
FileInputStream("filename").use {
  ...
}

fun foo(@dedicated x : X)   // Foo can be only called if x can be guaranteed to be a 
```

However, 
