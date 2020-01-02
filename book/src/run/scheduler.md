### Model-Finding Scheduler

Use the `--scheduler` option to choose how Razor processes search branches. The `fifo` scheduler (the default scheduler)
schedules new branches last and is a more suitable option for processing theories with few small satisfying models.
The `lifo` scheduler schedules new branches first, and is more suitable for processing theories with many large models.

```
razor solve -i <input> --scheduler <fifo/lifo>
```