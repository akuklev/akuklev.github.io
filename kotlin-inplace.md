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

However, this requirements are not sufficient to ensure correctness because of capturing: a reference to a pending object could be captured as an element in some list, inside of some field some object, or as a variable inside a closure which could be run as a separate job. We have to ensure that these jobs are finished and these objects either finalized or inaccessible before we finalize the object. Before we introduce the type-based capture checking mechanism that can ensure this, let us consider another use case requiring capture checking.

Capture Checking
----------------




Inplace objects
---------------


Stati
Sometimes it is desirable to pass an object as argument without allowing to capture or expose it:
```
fun foo(@inplace x : X)     // `x` can be only used inside `foo` while `foo` is executed,
                            // `x` cannot be captured or passed as non-inplace argument
```

To control proliferation of references, 

fun foo(@dedicated x : X)   // `x` is required to be a unique reference to the object



If `x` was created locally, obtained as a `dedicated` argument or a `dedicated` return value, and had not been not captured nor passed outside (except as an `@inplace`-argument), we can be sure it is a unique reference and therefore pass it as `dedicated` argument or return as a `dedicated` return value.





Let us introduce several annotations . 
Let us introduce the annotations `@Finalizes` and `@Pending`

We propose introducing several new annotations and interfaces to ensure correctness statically:
```
fun foo(@dedicated x : X)   // `x` is required to be a unique reference to the object

fun foo(@inplace x : X)     // `x` can be only used inside `foo` while `foo` is executed,
                            // `x` cannot be captured or passed outside

fun foo(@pending block : (T)-> R)   // `block` must be invoked at least once
fun foo(@once block : (T)-> R)      // `block` must be invoked exactly once: implies both @pending and @inplace
```




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
