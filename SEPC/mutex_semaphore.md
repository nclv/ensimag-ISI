See [this](https://www.guru99.com/mutex-vs-semaphore.html) list of differences.

Only one task can acquire the **mutex**. So, there is ownership associated with a mutex, and only the owner can release the mutex. Mutexes are just _simple locks obtained before entering its critical section_ and then releasing it. Since _only one thread is in its critical section_ at any given time, there are no race conditions, and data always remain consistent.

# Q1.

