/*
 * Copyright (c) 2017, Hisao Tamaki
*/

package tw.heuristic;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;

public class CPUTimer {
  private long threadTimeStart;
  private long gcTimeStart;
  private int timeout;
  
  ThreadMXBean threadMXBean;
  public CPUTimer() {
    threadMXBean = ManagementFactory.getThreadMXBean();
    threadTimeStart = threadMXBean.getCurrentThreadCpuTime();
    gcTimeStart = gcTime();
  }
  
  public void setTimeout(int timeout) {
    this.timeout = timeout;
  }
  
  public long getThreadTime() {
    long ct = threadMXBean.getCurrentThreadCpuTime();
    return (ct - threadTimeStart) / 1000000;
  }
  
  public long getGCTime() {
    return gcTime() - gcTimeStart;
  }
  
  public long getTime() {
    return getThreadTime() + getGCTime();
  }
  
  private long gcTime() {
    long gcTime = 0;

    for(GarbageCollectorMXBean gc :
            ManagementFactory.getGarbageCollectorMXBeans()) {

        long time = gc.getCollectionTime();

        if(time >= 0) {
            gcTime += time;
        }
    }
    return gcTime;
  }

  public boolean hasTimedOut() {
    return getTime() >= ((long) timeout) * 1000;
  }
}
