/* JamSort.java
 * Super scalar parallel samplesort with optimal oversampling.
 */

/*******************************************************************************
 * Copyright (C) 2019-2023 Snorri Agnarsson <snorri@hi.is>
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.

 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *******************************************************************************/

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class JamSort
{
    private final static int MAXPIVCOUNT_OBJECT = 1023;
    private final static int MINPIVCOUNT_OBJECT = 255;
    private final static int PARALLELCUTOFF_OBJECT = 2048;
    private static final int LOWSORTCUTOFF_OBJECT = 4096;

    private final static int MAXPIVCOUNT_DOUBLE = 1023;
    private final static int MINPIVCOUNT_DOUBLE = 255;
    private final static int PARALLELCUTOFF_DOUBLE = 10000;
    private final static int LOWSORTCUTOFF_DOUBLE = 2048;

    private final static int MAXPIVCOUNT_LONG = 1023;
    private final static int MINPIVCOUNT_LONG = 255;
    private final static int PARALLELCUTOFF_LONG = 10000;
    private final static int LOWSORTCUTOFF_LONG = 2048;

    private final static int MAXPIVCOUNT_INT = 1023;
    private final static int MINPIVCOUNT_INT = 511;
    private final static int PARALLELCUTOFF_INT = 8192;
    private static final int LOWSORTCUTOFF_INT = 8192;

    private final static int MAXPIVCOUNT_FLOAT = 1023;
    private final static int MINPIVCOUNT_FLOAT = 511;
    private final static int PARALLELCUTOFF_FLOAT = 8192;
    private final static int LOWSORTCUTOFF_FLOAT = 8192;

    private final static int THREADS = Runtime.getRuntime().availableProcessors();
    private static final int SERIALCUTOFF = 4096;

    private static class MyRand
    {
        private long mySeed = 1234567890123456789L;
        public final int rand( int n )
        {
            int x = (int)(mySeed >>> 16);
            mySeed = (mySeed * 0x5DEECE66DL + 0xBL) & ((1L << 48) - 1);
            return (x & 0x7FFFFFFF)%n;
        }
    }

    private static final class MyRandLocal extends ThreadLocal<MyRand>
    {
        @Override protected MyRand initialValue() { return new MyRand(); }
    }
    private static final MyRandLocal threadLocalRand = new MyRandLocal();
    
    private final static int rand( int n )
    {
        return threadLocalRand.get().rand(n);
    }

    public static final int oversampling( int len, int pivcount, int threadcount )
    {
        if( len < 65536 ) return 1;
        // Near-optimal formula for minimizing average comparison count per entropy reduction
        int OVERSAMPLING = (int)(Math.sqrt((1.0*len*pivcount)/(2.0*(1.0+pivcount)*(1.0+pivcount)*threadcount*Math.log(1.0+pivcount)))+0.4);
        if( OVERSAMPLING<1 ) OVERSAMPLING=1;
        return OVERSAMPLING;
    }

    private static<E extends Comparable<? super E>> E[] extractPivots( E[] a, int i, int j, int t )
    {
        final int len = j-i;
        int pivcount = MAXPIVCOUNT_OBJECT;

        // Try to distribute the entropy reduction work evenly between the last
        // two to three passes over the array.
        if( len < (MAXPIVCOUNT_OBJECT+1)*(MAXPIVCOUNT_OBJECT+1)*2 )
        {
            // We will need one more samplesort partition pass, followed by sorting
            // the resulting segments
            while( pivcount > MINPIVCOUNT_OBJECT && len < (pivcount/2+1)*(pivcount/2+1) ) pivcount /= 2;
        }
        else
        {
            // Otherwise we will probably need more than two samplesort partition passes.
            // so we will use MAXPIVCOUNT as the value for pivcount, assuming that MAXPIVCOUNT
            // is at the good upper edge of feasible pivot counts.
            pivcount = MAXPIVCOUNT_OBJECT;
        }

        E[] p = (E[])new Comparable<?>[pivcount];
        int OVERSAMPLING = oversampling(j-i,pivcount,t);
        if( OVERSAMPLING==1 )
        {
            for( int k=0 ; k!=p.length ; k++ ) p[k] = a[i+rand(j-i)];
            java.util.Arrays.sort(p,0,pivcount);
            return p;
        }
        E[] sample = (E[])new Comparable<?>[pivcount*OVERSAMPLING+OVERSAMPLING-1];
        for( int k=0 ; k!=sample.length ; k++ ) sample[k] = a[i+rand(j-i)];
        java.util.Arrays.sort(sample);
        for( int k=0 ; k!=pivcount ; k++ ) p[k] = sample[(k+1)*OVERSAMPLING-1];
        return p;
    }

    private static double[] extractPivots( double[] a, int i, int j, int t )
    {
        final int len = j-i;
        int pivcount = MAXPIVCOUNT_DOUBLE;

        // Try to distribute the entropy reduction work evenly between the last
        // two to three passes over the array.
        if( len < (MAXPIVCOUNT_DOUBLE+1)*(MAXPIVCOUNT_DOUBLE+1)*2 )
        {
            // We will need one more samplesort partition pass, followed by sorting
            // the resulting segments
            while( pivcount > MINPIVCOUNT_DOUBLE && len < (pivcount/2+1)*(pivcount/2+1) ) pivcount /= 2;
        }
        else
        {
            // Otherwise we will probably need more than two samplesort partition passes.
            // so we will use MAXPIVCOUNT as the value for pivcount, assuming that MAXPIVCOUNT
            // is at the good upper edge of feasible pivot counts.
            pivcount = MAXPIVCOUNT_DOUBLE;
        }

        double[] p = new double[pivcount];
        int OVERSAMPLING = oversampling(j-i,pivcount,t);
        if( OVERSAMPLING==1 )
        {
            for( int k=0 ; k!=p.length ; k++ ) p[k] = a[i+rand(j-i)];
            java.util.Arrays.sort(p,0,pivcount);
            return p;
        }
        double[] sample = new double[pivcount*OVERSAMPLING+OVERSAMPLING-1];
        for( int k=0 ; k!=sample.length ; k++ ) sample[k] = a[i+rand(j-i)];
        java.util.Arrays.sort(sample);
        for( int k=0 ; k!=pivcount ; k++ ) p[k] = sample[(k+1)*OVERSAMPLING-1];
        return p;
    }

    private static long[] extractPivots( long[] a, int i, int j, int t )
    {
        final int len = j-i;
        int pivcount = MAXPIVCOUNT_LONG;

        // Try to distribute the entropy reduction work evenly between the last
        // two to three passes over the array.
        if( len < (MAXPIVCOUNT_LONG+1)*(MAXPIVCOUNT_LONG+1)*2 )
        {
            // We will need one more samplesort partition pass, followed by sorting
            // the resulting segments
            while( pivcount > MINPIVCOUNT_LONG && len < (pivcount/2+1)*(pivcount/2+1) ) pivcount /= 2;
        }
        else
        {
            // Otherwise we will probably need more than two samplesort partition passes.
            // so we will use MAXPIVCOUNT as the value for pivcount, assuming that MAXPIVCOUNT
            // is at the good upper edge of feasible pivot counts.
            pivcount = MAXPIVCOUNT_LONG;
        }

        long[] p = new long[pivcount];
        int OVERSAMPLING = oversampling(j-i,pivcount,t);
        if( OVERSAMPLING==1 )
        {
            for( int k=0 ; k!=p.length ; k++ ) p[k] = a[i+rand(j-i)];
            java.util.Arrays.sort(p,0,pivcount);
            return p;
        }
        long[] sample = new long[pivcount*OVERSAMPLING+OVERSAMPLING-1];
        for( int k=0 ; k!=sample.length ; k++ ) sample[k] = a[i+rand(j-i)];
        java.util.Arrays.sort(sample);
        for( int k=0 ; k!=pivcount ; k++ ) p[k] = sample[(k+1)*OVERSAMPLING-1];
        return p;
    }

    private static float[] extractPivots( float[] a, int i, int j, int t )
    {
        final int len = j-i;
        int pivcount = MAXPIVCOUNT_FLOAT;

        // Try to distribute the entropy reduction work evenly between the last
        // two to three passes over the array.
        if( len < (MAXPIVCOUNT_FLOAT+1)*(MAXPIVCOUNT_FLOAT+1)*2 )
        {
            // We will need one more samplesort partition pass, followed by sorting
            // the resulting segments
            while( pivcount > MINPIVCOUNT_FLOAT && len < (pivcount/2+1)*(pivcount/2+1) ) pivcount /= 2;
        }
        else
        {
            // Otherwise we will probably need more than two samplesort partition passes.
            // so we will use MAXPIVCOUNT as the value for pivcount, assuming that MAXPIVCOUNT
            // is at the good upper edge of feasible pivot counts.
            pivcount = MAXPIVCOUNT_FLOAT;
        }

        float[] p = new float[pivcount];
        int OVERSAMPLING = oversampling(j-i,pivcount,t);
        if( OVERSAMPLING==1 )
        {
            for( int k=0 ; k!=p.length ; k++ ) p[k] = a[i+rand(j-i)];
            java.util.Arrays.sort(p,0,pivcount);
            return p;
        }
        float[] sample = new float[pivcount*OVERSAMPLING+OVERSAMPLING-1];
        for( int k=0 ; k!=sample.length ; k++ ) sample[k] = a[i+rand(j-i)];
        java.util.Arrays.sort(sample);
        for( int k=0 ; k!=pivcount ; k++ ) p[k] = sample[(k+1)*OVERSAMPLING-1];
        return p;
    }

    private static int[] extractPivots( int[] a, int i, int j, int t )
    {
        final int len = j-i;
        int pivcount = MAXPIVCOUNT_INT;

        // Try to distribute the entropy reduction work evenly between the last
        // two to three passes over the array.
        if( len < (MAXPIVCOUNT_INT+1)*(MAXPIVCOUNT_INT+1)*2 )
        {
            // We will need one more samplesort partition pass, followed by sorting
            // the resulting segments
            while( pivcount > MINPIVCOUNT_INT && len < (pivcount/2+1)*(pivcount/2+1) ) pivcount /= 2;
        }
        else
        {
            // Otherwise we will probably need more than two samplesort partition passes.
            // so we will use MAXPIVCOUNT as the value for pivcount, assuming that MAXPIVCOUNT
            // is at the good upper edge of feasible pivot counts.
            pivcount = MAXPIVCOUNT_INT;
        }

        int[] p = new int[pivcount];
        int OVERSAMPLING = oversampling(j-i,pivcount,t);
        if( OVERSAMPLING==1 )
        {
            for( int k=0 ; k!=p.length ; k++ ) p[k] = a[i+rand(j-i)];
            java.util.Arrays.sort(p,0,pivcount);
            return p;
        }
        int[] sample = new int[pivcount*OVERSAMPLING+OVERSAMPLING-1];
        for( int k=0 ; k!=sample.length ; k++ ) sample[k] = a[i+rand(j-i)];
        java.util.Arrays.sort(sample);
        for( int k=0 ; k!=pivcount ; k++ ) p[k] = sample[(k+1)*OVERSAMPLING-1];
        return p;
    }

    // pivcount is 2^k-1 for some k>1
    private final static<E extends Comparable<? super E>> void serialPartition( E[] a, int apos, E[] ap, int appos, short[] b, E[] p, int len, int[] x, boolean targeta, int pivcount )
    {
        if( pivcount==1 )
        {
            throw new Error("Attempting to use a single pivot. This is not supported.");
        }
        java.util.Arrays.fill(x,0);
        int i0,i1,i2,i3;
        int c0,c1,c2,c3;
        int n,np;
        E x0,x1,x2,x3;
        int ii=apos, jj=targeta?appos:apos,count=len;
        for( ; count>=4 ; count-=4 )
        {
            x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
            ii += 4;
            n = pivcount>>1;
            np = n+1;
            c0 = p[n].compareTo(x0);
            c1 = p[n].compareTo(x1);
            c2 = p[n].compareTo(x2);
            c3 = p[n].compareTo(x3);
            i0 = c0<0?np:0;
            i1 = c1<0?np:0;
            i2 = c2<0?np:0;
            i3 = c3<0?np:0;
            while( n!=1 )
            {
                // | <xK | ?? | >=xK |
                //        ^    ^
                //        iK   iK+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                c0 = p[i0+n].compareTo(x0);
                c1 = p[i1+n].compareTo(x1);
                c2 = p[i2+n].compareTo(x2);
                c3 = p[i3+n].compareTo(x3);
                i0 += c0<0?np:0;
                i1 += c1<0?np:0;
                i2 += c2<0?np:0;
                i3 += c3<0?np:0;
            }
            c0 = p[i0].compareTo(x0);
            c1 = p[i1].compareTo(x1);
            c2 = p[i2].compareTo(x2);
            c3 = p[i3].compareTo(x3);
            i0 += c0<=0?1:0;
            i1 += c1<=0?1:0;
            i2 += c2<=0?1:0;
            i3 += c3<=0?1:0;
            b[jj+0] = (short)i0;
            x[i0]++;
            b[jj+1] = (short)i1;
            x[i1]++;
            b[jj+2] = (short)i2;
            x[i2]++;
            b[jj+3] = (short)i3;
            x[i3]++;
            jj += 4;
        }
        while( count-- != 0 )
        {
            i0=0;
            x0=a[ii++];
            n = pivcount;
            while( n!=1 )
            {
                // | <x | ?? | >=x |
                //       ^    ^
                //       i0   i0+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n].compareTo(x0)<0?np:0;
            }
            i0 += p[i0].compareTo(x0)<=0?1:0;
            b[jj++] = (short)i0;
            x[i0]++;
        }
        int tmp, pos = appos;
        for( int k=0 ; k!=x.length ; k++ )
        {
            tmp = x[k];
            x[k] = pos;
            pos += tmp;
        }
        ii = apos;
        jj = targeta?appos:apos;
        count = len;
        while( count >= 16 )
        {
            count -= 16;
            ap[x[b[jj+0]]++] = a[ii+0];
            ap[x[b[jj+1]]++] = a[ii+1];
            ap[x[b[jj+2]]++] = a[ii+2];
            ap[x[b[jj+3]]++] = a[ii+3];
            ap[x[b[jj+4]]++] = a[ii+4];
            ap[x[b[jj+5]]++] = a[ii+5];
            ap[x[b[jj+6]]++] = a[ii+6];
            ap[x[b[jj+7]]++] = a[ii+7];
            ap[x[b[jj+8]]++] = a[ii+8];
            ap[x[b[jj+9]]++] = a[ii+9];
            ap[x[b[jj+10]]++] = a[ii+10];
            ap[x[b[jj+11]]++] = a[ii+11];
            ap[x[b[jj+12]]++] = a[ii+12];
            ap[x[b[jj+13]]++] = a[ii+13];
            ap[x[b[jj+14]]++] = a[ii+14];
            ap[x[b[jj+15]]++] = a[ii+15];
            ii += 16;
            jj += 16;
        }
        while( count != 0 )
        {
            count--;
            ap[x[b[jj++]]++] = a[ii++];
        }
    }

    // pivcount is one of 3, 7, 15, 31, 63, 127, 255
    private final static void serialPartition( double[] a, int apos, double[] ap, int appos, short[] b, double[] p, int len, int[] x, boolean targeta, int pivcount )
    {
        if( pivcount==1 )
        {
            throw new Error("Attempting to use a single pivot. This is not supported.");
        }
        java.util.Arrays.fill(x,0);
        int i0,i1,i2,i3,i4,i5,i6,i7;
        int i8,i9,iA,iB,iC,iD,iE,iF;
        int n,np;
        double x0,x1,x2,x3,x4,x5,x6,x7;
        double x8,x9,xA,xB,xC,xD,xE,xF;
        int ii=apos, jj=targeta?appos:apos,count=len;
        for( ; count>=16 ; count-=16 )
        {
            x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
            x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
            x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
            xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
            ii += 16;
            n = pivcount>>1;
            np = n+1;
            i0 = p[n]<x0?np:0;
            i1 = p[n]<x1?np:0;
            i2 = p[n]<x2?np:0;
            i3 = p[n]<x3?np:0;
            i4 = p[n]<x4?np:0;
            i5 = p[n]<x5?np:0;
            i6 = p[n]<x6?np:0;
            i7 = p[n]<x7?np:0;
            i8 = p[n]<x8?np:0;
            i9 = p[n]<x9?np:0;
            iA = p[n]<xA?np:0;
            iB = p[n]<xB?np:0;
            iC = p[n]<xC?np:0;
            iD = p[n]<xD?np:0;
            iE = p[n]<xE?np:0;
            iF = p[n]<xF?np:0;
            while( n!=1 )
            {
                // | <xK | ?? | >=xK |
                //        ^    ^
                //        iK   iK+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
                i1 += p[i1+n]<x1?np:0;
                i2 += p[i2+n]<x2?np:0;
                i3 += p[i3+n]<x3?np:0;
                i4 += p[i4+n]<x4?np:0;
                i5 += p[i5+n]<x5?np:0;
                i6 += p[i6+n]<x6?np:0;
                i7 += p[i7+n]<x7?np:0;
                i8 += p[i8+n]<x8?np:0;
                i9 += p[i9+n]<x9?np:0;
                iA += p[iA+n]<xA?np:0;
                iB += p[iB+n]<xB?np:0;
                iC += p[iC+n]<xC?np:0;
                iD += p[iD+n]<xD?np:0;
                iE += p[iE+n]<xE?np:0;
                iF += p[iF+n]<xF?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            i1 += p[i1]<=x1?1:0;
            i2 += p[i2]<=x2?1:0;
            i3 += p[i3]<=x3?1:0;
            i4 += p[i4]<=x4?1:0;
            i5 += p[i5]<=x5?1:0;
            i6 += p[i6]<=x6?1:0;
            i7 += p[i7]<=x7?1:0;
            i8 += p[i8]<=x8?1:0;
            i9 += p[i9]<=x9?1:0;
            iA += p[iA]<=xA?1:0;
            iB += p[iB]<=xB?1:0;
            iC += p[iC]<=xC?1:0;
            iD += p[iD]<=xD?1:0;
            iE += p[iE]<=xE?1:0;
            iF += p[iF]<=xF?1:0;
            b[jj+0] = (short)i0;
            x[i0]++;
            b[jj+1] = (short)i1;
            x[i1]++;
            b[jj+2] = (short)i2;
            x[i2]++;
            b[jj+3] = (short)i3;
            x[i3]++;
            b[jj+4] = (short)i4;
            x[i4]++;
            b[jj+5] = (short)i5;
            x[i5]++;
            b[jj+6] = (short)i6;
            x[i6]++;
            b[jj+7] = (short)i7;
            x[i7]++;
            b[jj+8] = (short)i8;
            x[i8]++;
            b[jj+9] = (short)i9;
            x[i9]++;
            b[jj+10] = (short)iA;
            x[iA]++;
            b[jj+11] = (short)iB;
            x[iB]++;
            b[jj+12] = (short)iC;
            x[iC]++;
            b[jj+13] = (short)iD;
            x[iD]++;
            b[jj+14] = (short)iE;
            x[iE]++;
            b[jj+15] = (short)iF;
            x[iF]++;
            jj += 16;
        }
        while( count-- != 0 )
        {
            i0=0;
            x0=a[ii++];
            n = pivcount;
            while( n!=1 )
            {
                // | <x | ?? | >=x |
                //       ^    ^
                //       i0   i0+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            b[jj++] = (short)i0;
            x[i0]++;
        }
        int tmp, pos = appos;
        for( int k=0 ; k!=x.length ; k++ )
        {
            tmp = x[k];
            x[k] = pos;
            pos += tmp;
        }
        ii = apos;
        jj = targeta?appos:apos;
        count = len;
        while( count >= 16 )
        {
            count -= 16;
            ap[x[b[jj+0]]++] = a[ii+0];
            ap[x[b[jj+1]]++] = a[ii+1];
            ap[x[b[jj+2]]++] = a[ii+2];
            ap[x[b[jj+3]]++] = a[ii+3];
            ap[x[b[jj+4]]++] = a[ii+4];
            ap[x[b[jj+5]]++] = a[ii+5];
            ap[x[b[jj+6]]++] = a[ii+6];
            ap[x[b[jj+7]]++] = a[ii+7];
            ap[x[b[jj+8]]++] = a[ii+8];
            ap[x[b[jj+9]]++] = a[ii+9];
            ap[x[b[jj+10]]++] = a[ii+10];
            ap[x[b[jj+11]]++] = a[ii+11];
            ap[x[b[jj+12]]++] = a[ii+12];
            ap[x[b[jj+13]]++] = a[ii+13];
            ap[x[b[jj+14]]++] = a[ii+14];
            ap[x[b[jj+15]]++] = a[ii+15];
            ii += 16;
            jj += 16;
        }
        while( count != 0 )
        {
            count--;
            ap[x[b[jj++]]++] = a[ii++];
        }
    }

    // pivcount is one of 3, 7, 15, 31, 63, 127, 255
    private final static void serialPartition( long[] a, int apos, long[] ap, int appos, short[] b, long[] p, int len, int[] x, boolean targeta, int pivcount )
    {
        if( pivcount==1 )
        {
            throw new Error("Attempting to use a single pivot. This is not supported.");
        }
        java.util.Arrays.fill(x,0);
        int i0,i1,i2,i3,i4,i5,i6,i7;
        int i8,i9,iA,iB,iC,iD,iE,iF;
        int n,np;
        long x0,x1,x2,x3,x4,x5,x6,x7;
        long x8,x9,xA,xB,xC,xD,xE,xF;
        int ii=apos, jj=targeta?appos:apos,count=len;
        for( ; count>=16 ; count-=16 )
        {
            x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
            x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
            x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
            xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
            ii += 16;
            n = pivcount>>1;
            np = n+1;
            i0 = p[n]<x0?np:0;
            i1 = p[n]<x1?np:0;
            i2 = p[n]<x2?np:0;
            i3 = p[n]<x3?np:0;
            i4 = p[n]<x4?np:0;
            i5 = p[n]<x5?np:0;
            i6 = p[n]<x6?np:0;
            i7 = p[n]<x7?np:0;
            i8 = p[n]<x8?np:0;
            i9 = p[n]<x9?np:0;
            iA = p[n]<xA?np:0;
            iB = p[n]<xB?np:0;
            iC = p[n]<xC?np:0;
            iD = p[n]<xD?np:0;
            iE = p[n]<xE?np:0;
            iF = p[n]<xF?np:0;
            while( n!=1 )
            {
                // | <xK | ?? | >=xK |
                //        ^    ^
                //        iK   iK+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
                i1 += p[i1+n]<x1?np:0;
                i2 += p[i2+n]<x2?np:0;
                i3 += p[i3+n]<x3?np:0;
                i4 += p[i4+n]<x4?np:0;
                i5 += p[i5+n]<x5?np:0;
                i6 += p[i6+n]<x6?np:0;
                i7 += p[i7+n]<x7?np:0;
                i8 += p[i8+n]<x8?np:0;
                i9 += p[i9+n]<x9?np:0;
                iA += p[iA+n]<xA?np:0;
                iB += p[iB+n]<xB?np:0;
                iC += p[iC+n]<xC?np:0;
                iD += p[iD+n]<xD?np:0;
                iE += p[iE+n]<xE?np:0;
                iF += p[iF+n]<xF?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            i1 += p[i1]<=x1?1:0;
            i2 += p[i2]<=x2?1:0;
            i3 += p[i3]<=x3?1:0;
            i4 += p[i4]<=x4?1:0;
            i5 += p[i5]<=x5?1:0;
            i6 += p[i6]<=x6?1:0;
            i7 += p[i7]<=x7?1:0;
            i8 += p[i8]<=x8?1:0;
            i9 += p[i9]<=x9?1:0;
            iA += p[iA]<=xA?1:0;
            iB += p[iB]<=xB?1:0;
            iC += p[iC]<=xC?1:0;
            iD += p[iD]<=xD?1:0;
            iE += p[iE]<=xE?1:0;
            iF += p[iF]<=xF?1:0;
            b[jj+0] = (short)i0;
            x[i0]++;
            b[jj+1] = (short)i1;
            x[i1]++;
            b[jj+2] = (short)i2;
            x[i2]++;
            b[jj+3] = (short)i3;
            x[i3]++;
            b[jj+4] = (short)i4;
            x[i4]++;
            b[jj+5] = (short)i5;
            x[i5]++;
            b[jj+6] = (short)i6;
            x[i6]++;
            b[jj+7] = (short)i7;
            x[i7]++;
            b[jj+8] = (short)i8;
            x[i8]++;
            b[jj+9] = (short)i9;
            x[i9]++;
            b[jj+10] = (short)iA;
            x[iA]++;
            b[jj+11] = (short)iB;
            x[iB]++;
            b[jj+12] = (short)iC;
            x[iC]++;
            b[jj+13] = (short)iD;
            x[iD]++;
            b[jj+14] = (short)iE;
            x[iE]++;
            b[jj+15] = (short)iF;
            x[iF]++;
            jj += 16;
        }
        while( count-- != 0 )
        {
            i0=0;
            x0=a[ii++];
            n = pivcount;
            while( n!=1 )
            {
                // | <x | ?? | >=x |
                //       ^    ^
                //       i0   i0+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            b[jj++] = (short)i0;
            x[i0]++;
        }
        int tmp, pos = appos;
        for( int k=0 ; k!=x.length ; k++ )
        {
            tmp = x[k];
            x[k] = pos;
            pos += tmp;
        }
        ii = apos;
        jj = targeta?appos:apos;
        count = len;
        while( count >= 16 )
        {
            count -= 16;
            ap[x[b[jj+0]]++] = a[ii+0];
            ap[x[b[jj+1]]++] = a[ii+1];
            ap[x[b[jj+2]]++] = a[ii+2];
            ap[x[b[jj+3]]++] = a[ii+3];
            ap[x[b[jj+4]]++] = a[ii+4];
            ap[x[b[jj+5]]++] = a[ii+5];
            ap[x[b[jj+6]]++] = a[ii+6];
            ap[x[b[jj+7]]++] = a[ii+7];
            ap[x[b[jj+8]]++] = a[ii+8];
            ap[x[b[jj+9]]++] = a[ii+9];
            ap[x[b[jj+10]]++] = a[ii+10];
            ap[x[b[jj+11]]++] = a[ii+11];
            ap[x[b[jj+12]]++] = a[ii+12];
            ap[x[b[jj+13]]++] = a[ii+13];
            ap[x[b[jj+14]]++] = a[ii+14];
            ap[x[b[jj+15]]++] = a[ii+15];
            ii += 16;
            jj += 16;
        }
        while( count != 0 )
        {
            count--;
            ap[x[b[jj++]]++] = a[ii++];
        }
    }

    // pivcount is one of 3, 7, 15, 31, 63, 127, 255
    private final static void serialPartition( float[] a, int apos, float[] ap, int appos, short[] b, float[] p, int len, int[] x, boolean targeta, int pivcount )
    {
        if( pivcount==1 )
        {
            throw new Error("Attempting to use a single pivot. This is not supported.");
        }
        java.util.Arrays.fill(x,0);
        int i0,i1,i2,i3,i4,i5,i6,i7;
        int i8,i9,iA,iB,iC,iD,iE,iF;
        int n,np;
        float x0,x1,x2,x3,x4,x5,x6,x7;
        float x8,x9,xA,xB,xC,xD,xE,xF;
        int ii=apos, jj=targeta?appos:apos,count=len;
        for( ; count>=16 ; count-=16 )
        {
            x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
            x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
            x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
            xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
            ii += 16;
            n = pivcount>>1;
            np = n+1;
            i0 = p[n]<x0?np:0;
            i1 = p[n]<x1?np:0;
            i2 = p[n]<x2?np:0;
            i3 = p[n]<x3?np:0;
            i4 = p[n]<x4?np:0;
            i5 = p[n]<x5?np:0;
            i6 = p[n]<x6?np:0;
            i7 = p[n]<x7?np:0;
            i8 = p[n]<x8?np:0;
            i9 = p[n]<x9?np:0;
            iA = p[n]<xA?np:0;
            iB = p[n]<xB?np:0;
            iC = p[n]<xC?np:0;
            iD = p[n]<xD?np:0;
            iE = p[n]<xE?np:0;
            iF = p[n]<xF?np:0;
            while( n!=1 )
            {
                // | <xK | ?? | >=xK |
                //        ^    ^
                //        iK   iK+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
                i1 += p[i1+n]<x1?np:0;
                i2 += p[i2+n]<x2?np:0;
                i3 += p[i3+n]<x3?np:0;
                i4 += p[i4+n]<x4?np:0;
                i5 += p[i5+n]<x5?np:0;
                i6 += p[i6+n]<x6?np:0;
                i7 += p[i7+n]<x7?np:0;
                i8 += p[i8+n]<x8?np:0;
                i9 += p[i9+n]<x9?np:0;
                iA += p[iA+n]<xA?np:0;
                iB += p[iB+n]<xB?np:0;
                iC += p[iC+n]<xC?np:0;
                iD += p[iD+n]<xD?np:0;
                iE += p[iE+n]<xE?np:0;
                iF += p[iF+n]<xF?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            i1 += p[i1]<=x1?1:0;
            i2 += p[i2]<=x2?1:0;
            i3 += p[i3]<=x3?1:0;
            i4 += p[i4]<=x4?1:0;
            i5 += p[i5]<=x5?1:0;
            i6 += p[i6]<=x6?1:0;
            i7 += p[i7]<=x7?1:0;
            i8 += p[i8]<=x8?1:0;
            i9 += p[i9]<=x9?1:0;
            iA += p[iA]<=xA?1:0;
            iB += p[iB]<=xB?1:0;
            iC += p[iC]<=xC?1:0;
            iD += p[iD]<=xD?1:0;
            iE += p[iE]<=xE?1:0;
            iF += p[iF]<=xF?1:0;
            b[jj+0] = (short)i0;
            x[i0]++;
            b[jj+1] = (short)i1;
            x[i1]++;
            b[jj+2] = (short)i2;
            x[i2]++;
            b[jj+3] = (short)i3;
            x[i3]++;
            b[jj+4] = (short)i4;
            x[i4]++;
            b[jj+5] = (short)i5;
            x[i5]++;
            b[jj+6] = (short)i6;
            x[i6]++;
            b[jj+7] = (short)i7;
            x[i7]++;
            b[jj+8] = (short)i8;
            x[i8]++;
            b[jj+9] = (short)i9;
            x[i9]++;
            b[jj+10] = (short)iA;
            x[iA]++;
            b[jj+11] = (short)iB;
            x[iB]++;
            b[jj+12] = (short)iC;
            x[iC]++;
            b[jj+13] = (short)iD;
            x[iD]++;
            b[jj+14] = (short)iE;
            x[iE]++;
            b[jj+15] = (short)iF;
            x[iF]++;
            jj += 16;
        }
        while( count-- != 0 )
        {
            i0=0;
            x0=a[ii++];
            n = pivcount;
            while( n!=1 )
            {
                // | <x | ?? | >=x |
                //       ^    ^
                //       i0   i0+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            b[jj++] = (short)i0;
            x[i0]++;
        }
        int tmp, pos = appos;
        for( int k=0 ; k!=x.length ; k++ )
        {
            tmp = x[k];
            x[k] = pos;
            pos += tmp;
        }
        ii = apos;
        jj = targeta?appos:apos;
        count = len;
        while( count >= 16 )
        {
            count -= 16;
            ap[x[b[jj+0]]++] = a[ii+0];
            ap[x[b[jj+1]]++] = a[ii+1];
            ap[x[b[jj+2]]++] = a[ii+2];
            ap[x[b[jj+3]]++] = a[ii+3];
            ap[x[b[jj+4]]++] = a[ii+4];
            ap[x[b[jj+5]]++] = a[ii+5];
            ap[x[b[jj+6]]++] = a[ii+6];
            ap[x[b[jj+7]]++] = a[ii+7];
            ap[x[b[jj+8]]++] = a[ii+8];
            ap[x[b[jj+9]]++] = a[ii+9];
            ap[x[b[jj+10]]++] = a[ii+10];
            ap[x[b[jj+11]]++] = a[ii+11];
            ap[x[b[jj+12]]++] = a[ii+12];
            ap[x[b[jj+13]]++] = a[ii+13];
            ap[x[b[jj+14]]++] = a[ii+14];
            ap[x[b[jj+15]]++] = a[ii+15];
            ii += 16;
            jj += 16;
        }
        while( count != 0 )
        {
            count--;
            ap[x[b[jj++]]++] = a[ii++];
        }
    }

    private final static void serialPartition( int[] a, int apos, int[] ap, int appos, short[] b, int[] p, int len, int[] x, boolean targeta, int pivcount )
    {
        if( pivcount==1 )
        {
            throw new Error("Attempting to use a single pivot. This is not supported.");
        }
        java.util.Arrays.fill(x,0);
        int i0,i1,i2,i3,i4,i5,i6,i7;
        int i8,i9,iA,iB,iC,iD,iE,iF;
        int n,np;
        int x0,x1,x2,x3,x4,x5,x6,x7;
        int x8,x9,xA,xB,xC,xD,xE,xF;
        int ii=apos, jj=targeta?appos:apos,count=len;
        for( ; count>=16 ; count-=16 )
        {
            x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
            x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
            x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
            xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
            ii += 16;
            n = pivcount>>1;
            np = n+1;
            i0 = p[n]<x0?np:0;
            i1 = p[n]<x1?np:0;
            i2 = p[n]<x2?np:0;
            i3 = p[n]<x3?np:0;
            i4 = p[n]<x4?np:0;
            i5 = p[n]<x5?np:0;
            i6 = p[n]<x6?np:0;
            i7 = p[n]<x7?np:0;
            i8 = p[n]<x8?np:0;
            i9 = p[n]<x9?np:0;
            iA = p[n]<xA?np:0;
            iB = p[n]<xB?np:0;
            iC = p[n]<xC?np:0;
            iD = p[n]<xD?np:0;
            iE = p[n]<xE?np:0;
            iF = p[n]<xF?np:0;
            while( n!=1 )
            {
                // | <xK | ?? | >=xK |
                //        ^    ^
                //        iK   iK+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
                i1 += p[i1+n]<x1?np:0;
                i2 += p[i2+n]<x2?np:0;
                i3 += p[i3+n]<x3?np:0;
                i4 += p[i4+n]<x4?np:0;
                i5 += p[i5+n]<x5?np:0;
                i6 += p[i6+n]<x6?np:0;
                i7 += p[i7+n]<x7?np:0;
                i8 += p[i8+n]<x8?np:0;
                i9 += p[i9+n]<x9?np:0;
                iA += p[iA+n]<xA?np:0;
                iB += p[iB+n]<xB?np:0;
                iC += p[iC+n]<xC?np:0;
                iD += p[iD+n]<xD?np:0;
                iE += p[iE+n]<xE?np:0;
                iF += p[iF+n]<xF?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            i1 += p[i1]<=x1?1:0;
            i2 += p[i2]<=x2?1:0;
            i3 += p[i3]<=x3?1:0;
            i4 += p[i4]<=x4?1:0;
            i5 += p[i5]<=x5?1:0;
            i6 += p[i6]<=x6?1:0;
            i7 += p[i7]<=x7?1:0;
            i8 += p[i8]<=x8?1:0;
            i9 += p[i9]<=x9?1:0;
            iA += p[iA]<=xA?1:0;
            iB += p[iB]<=xB?1:0;
            iC += p[iC]<=xC?1:0;
            iD += p[iD]<=xD?1:0;
            iE += p[iE]<=xE?1:0;
            iF += p[iF]<=xF?1:0;
            b[jj+0] = (short)i0;
            x[i0]++;
            b[jj+1] = (short)i1;
            x[i1]++;
            b[jj+2] = (short)i2;
            x[i2]++;
            b[jj+3] = (short)i3;
            x[i3]++;
            b[jj+4] = (short)i4;
            x[i4]++;
            b[jj+5] = (short)i5;
            x[i5]++;
            b[jj+6] = (short)i6;
            x[i6]++;
            b[jj+7] = (short)i7;
            x[i7]++;
            b[jj+8] = (short)i8;
            x[i8]++;
            b[jj+9] = (short)i9;
            x[i9]++;
            b[jj+10] = (short)iA;
            x[iA]++;
            b[jj+11] = (short)iB;
            x[iB]++;
            b[jj+12] = (short)iC;
            x[iC]++;
            b[jj+13] = (short)iD;
            x[iD]++;
            b[jj+14] = (short)iE;
            x[iE]++;
            b[jj+15] = (short)iF;
            x[iF]++;
            jj += 16;
        }
        while( count-- != 0 )
        {
            i0=0;
            x0=a[ii++];
            n = pivcount;
            while( n!=1 )
            {
                // | <x | ?? | >=x |
                //       ^    ^
                //       i0   i0+n
                // n>0 is of form 2^k-1
                n >>= 1;
                np = n+1;
                i0 += p[i0+n]<x0?np:0;
            }
            i0 += p[i0]<=x0?1:0;
            b[jj++] = (short)i0;
            x[i0]++;
        }
        int tmp, pos = appos;
        for( int k=0 ; k!=x.length ; k++ )
        {
            tmp = x[k];
            x[k] = pos;
            pos += tmp;
        }
        ii = apos;
        jj = targeta?appos:apos;
        count = len;
        while( count >= 16 )
        {
            count -= 16;
            ap[x[b[jj+0]]++] = a[ii+0];
            ap[x[b[jj+1]]++] = a[ii+1];
            ap[x[b[jj+2]]++] = a[ii+2];
            ap[x[b[jj+3]]++] = a[ii+3];
            ap[x[b[jj+4]]++] = a[ii+4];
            ap[x[b[jj+5]]++] = a[ii+5];
            ap[x[b[jj+6]]++] = a[ii+6];
            ap[x[b[jj+7]]++] = a[ii+7];
            ap[x[b[jj+8]]++] = a[ii+8];
            ap[x[b[jj+9]]++] = a[ii+9];
            ap[x[b[jj+10]]++] = a[ii+10];
            ap[x[b[jj+11]]++] = a[ii+11];
            ap[x[b[jj+12]]++] = a[ii+12];
            ap[x[b[jj+13]]++] = a[ii+13];
            ap[x[b[jj+14]]++] = a[ii+14];
            ap[x[b[jj+15]]++] = a[ii+15];
            ii += 16;
            jj += 16;
        }
        while( count != 0 )
        {
            count--;
            ap[x[b[jj++]]++] = a[ii++];
        }
    }

    private final static<E extends Comparable<? super E>> void lowSort( E[] a, int apos, E[] ap, int appos, short[] b, int len, boolean targeta )
    {
        if( len < LOWSORTCUTOFF_OBJECT )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }
        // Get pivots
        E[] p = extractPivots(a,apos,apos+len,1);
        if( p==null )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }

        int pivcount = p.length;
        // The number of pivots will be of form 2^k-1.

        int[] x = new int[pivcount+1];

        serialPartition(a,apos,ap,appos,b,p,len,x,targeta,pivcount);

        // Sort the resulting segments

        int t, u=x[0];
        int segoffset, seglength;
        seglength = u-appos;
        if( seglength > 0 )
            lowSort(ap,appos,a,apos,b,seglength,!targeta);
        for( int k=1 ; k!=x.length ; k++ )
        {
            t = u;
            u = x[k];
            segoffset = t-appos;
            seglength = u-t;
            if( k<pivcount && p[k-1].compareTo(p[k])==0 )
            {
                if( targeta ) System.arraycopy(ap,appos+segoffset,a,apos+segoffset,seglength);
            }
            else if( seglength > 0 )
                lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
        }
        segoffset = u-appos;
        seglength = len-segoffset;
        if( seglength > 0 )
            lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
    }

    private final static int twopow( int n )
    {
        int p = 1;
        while( n>0 ) { p<<=1; n--; }
        return p;
    }

    private final static int log2( int n )
    {
        int lg = 0;
        while( n>1 ) { lg++; n>>=1; }
        return lg;
    }

    private final static void lowSort( double[] a, int apos, double[] ap, int appos, short[] b, int len, boolean targeta )
    {
        if( len < LOWSORTCUTOFF_DOUBLE )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }
        // Get pivots
        double[] p = extractPivots(a,apos,apos+len,1);
        if( p==null )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }

        int pivcount = p.length;
        // The number of pivots will be of form 2^k-1.

        int[] x = new int[pivcount+1];

        serialPartition(a,apos,ap,appos,b,p,len,x,targeta,pivcount);

        // Sort the resulting segments

        int t, u=x[0];
        int segoffset, seglength;
        seglength = u-appos;
        if( seglength > 0 )
            lowSort(ap,appos,a,apos,b,seglength,!targeta);
        for( int k=1 ; k!=x.length ; k++ )
        {
            t = u;
            u = x[k];
            segoffset = t-appos;
            seglength = u-t;
            if( k<pivcount && p[k-1]==p[k] )
            {
                if( targeta ) System.arraycopy(ap,appos+segoffset,a,apos+segoffset,seglength);
            }
            else if( seglength > 0 )
                lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
        }
        segoffset = u-appos;
        seglength = len-segoffset;
        if( seglength > 0 )
            lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
    }

    private final static void lowSort( long[] a, int apos, long[] ap, int appos, short[] b, int len, boolean targeta )
    {
        if( len < LOWSORTCUTOFF_LONG )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }
        // Get pivots
        long[] p = extractPivots(a,apos,apos+len,1);
        if( p==null )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }

        int pivcount = p.length;
        // The number of pivots will be of form 2^k-1.

        int[] x = new int[pivcount+1];

        serialPartition(a,apos,ap,appos,b,p,len,x,targeta,pivcount);

        // Sort the resulting segments

        int t, u=x[0];
        int segoffset, seglength;
        seglength = u-appos;
        if( seglength > 0 )
            lowSort(ap,appos,a,apos,b,seglength,!targeta);
        for( int k=1 ; k!=x.length ; k++ )
        {
            t = u;
            u = x[k];
            segoffset = t-appos;
            seglength = u-t;
            if( k<pivcount && p[k-1]==p[k] )
            {
                if( targeta ) System.arraycopy(ap,appos+segoffset,a,apos+segoffset,seglength);
            }
            else if( seglength > 0 )
                lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
        }
        segoffset = u-appos;
        seglength = len-segoffset;
        if( seglength > 0 )
            lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
    }

    private final static void lowSort( float[] a, int apos, float[] ap, int appos, short[] b, int len, boolean targeta )
    {
        if( len < LOWSORTCUTOFF_FLOAT )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }
        // Get pivots
        float[] p = extractPivots(a,apos,apos+len,1);
        if( p==null )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }

        int pivcount = p.length;
        // The number of pivots will be of form 2^k-1.

        int[] x = new int[pivcount+1];

        serialPartition(a,apos,ap,appos,b,p,len,x,targeta,pivcount);

        // Sort the resulting segments

        int t, u=x[0];
        int segoffset, seglength;
        seglength = u-appos;
        if( seglength > 0 )
            lowSort(ap,appos,a,apos,b,seglength,!targeta);
        for( int k=1 ; k!=x.length ; k++ )
        {
            t = u;
            u = x[k];
            segoffset = t-appos;
            seglength = u-t;
            if( k<pivcount && p[k-1]==p[k] )
            {
                if( targeta ) System.arraycopy(ap,appos+segoffset,a,apos+segoffset,seglength);
            }
            else if( seglength > 0 )
                lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
        }
        segoffset = u-appos;
        seglength = len-segoffset;
        if( seglength > 0 )
            lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
    }

    private final static void lowSort( int[] a, int apos, int[] ap, int appos, short[] b, int len, boolean targeta )
    {
        if( len < LOWSORTCUTOFF_INT )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }
        // Get pivots
        int[] p = extractPivots(a,apos,apos+len,1);
        if( p==null )
        {
            lowestSort(a,apos,apos+len);
            if( !targeta ) System.arraycopy(a,apos,ap,appos,len);
            return;
        }

        int pivcount = p.length;
        // The number of pivots will be of form 2^k-1.

        int[] x = new int[pivcount+1];

        serialPartition(a,apos,ap,appos,b,p,len,x,targeta,pivcount);

        // Sort the resulting segments

        int t, u=x[0];
        int segoffset, seglength;
        seglength = u-appos;
        if( seglength > 0 )
            lowSort(ap,appos,a,apos,b,seglength,!targeta);
        for( int k=1 ; k!=x.length ; k++ )
        {
            t = u;
            u = x[k];
            segoffset = t-appos;
            seglength = u-t;
            if( k<pivcount && p[k-1]==p[k] )
            {
                if( targeta ) System.arraycopy(ap,appos+segoffset,a,apos+segoffset,seglength);
            }
            else if( seglength > 0 )
                lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
        }
        segoffset = u-appos;
        seglength = len-segoffset;
        if( seglength > 0 )
            lowSort(ap,appos+segoffset,a,apos+segoffset,b,seglength,!targeta);
    }

    private final static<E extends Comparable<? super E>> void lowestSort( E[] a, int i, int j )
    {
        java.util.Arrays.sort(a,i,j);
    }

    private final static void lowestSort( double[] a, int i, int j )
    {
        java.util.Arrays.sort(a,i,j);
    }

    private final static void lowestSort( long[] a, int i, int j )
    {
        java.util.Arrays.sort(a,i,j);
    }

    private final static void lowestSort( float[] a, int i, int j )
    {
        java.util.Arrays.sort(a,i,j);
    }

    private final static void lowestSort( int[] a, int i, int j )
    {
        java.util.Arrays.sort(a,i,j);
    }

    private final static<E extends Comparable<? super E>> void insertionSort( E[] a, int i, int j )
    {
        E tmp;
        int n, k = i;
        for( ; k<j ; k++ )
        {
            tmp = a[k];
            for( n=k ; n>i && a[n-1].compareTo(tmp)>0 ; n-- ) a[n]=a[n-1];
            a[n] = tmp;
        }
    }

    public static void serialSort( double[] a, int i, int j )
    {
        int len = j-i;
        if( len==0 ) return;
        if( len < SERIALCUTOFF )
        {
            java.util.Arrays.sort(a,i,j);
            return;
        }
        double[] ap = new double[len];
        short[] b = new short[len];
        lowSort(a,i,ap,0,b,len,true);
    }

    public static void serialSort( long[] a, int i, int j )
    {
        int len = j-i;
        if( len==0 ) return;
        if( len < SERIALCUTOFF )
        {
            java.util.Arrays.sort(a,i,j);
            return;
        }
        long[] ap = new long[len];
        short[] b = new short[len];
        lowSort(a,i,ap,0,b,len,true);
    }

    public static void serialSort( float[] a, int i, int j )
    {
        int len = j-i;
        if( len==0 ) return;
        if( len < SERIALCUTOFF )
        {
            java.util.Arrays.sort(a,i,j);
            return;
        }
        float[] ap = new float[len];
        short[] b = new short[len];
        lowSort(a,i,ap,0,b,len,true);
    }

    public static void serialSort( int[] a, int i, int j )
    {
        int len = j-i;
        if( len==0 ) return;
        if( len < SERIALCUTOFF )
        {
            java.util.Arrays.sort(a,i,j);
            return;
        }
        int[] ap = new int[len];
        short[] b = new short[len];
        lowSort(a,i,ap,0,b,len,true);
    }

    public static<E extends Comparable<? super E>> void serialSort( E[] a, int i, int j )
    {
        int len = j-i;
        if( len==0 ) return;
        if( len <= 1024 )
        {
            lowestSort(a,i,j);
            return;
        }
        E[] ap = (E[])new Comparable<?>[len];
        short[] b = new short[len];
        lowSort(a,i,ap,0,b,len,true);
    }

    public static void serialSort( double[] a )
    {
        serialSort(a,0,a.length);
    }

    public static void serialSort( float[] a )
    {
        serialSort(a,0,a.length);
    }

    public static void serialSort( int[] a )
    {
        serialSort(a,0,a.length);
    }

    public static<E extends Comparable<? super E>> void serialSort( E[] a )
    {
        serialSort(a,0,a.length);
    }

    static class DoneWaiter
    {
        private int count;
        public DoneWaiter( int count )
        {
            this.count = count;
        }
        public synchronized void signalOneDone()
        {
            if( --count==0 ) notifyAll();
        }
        public synchronized void waitUntilAllDone()
        {
            try
            {
                while( count!=0 ) wait();
            }
            catch( Exception e )
            {
                throw new Error(e);
            }
        }
    }

    static class DoublePartitioner implements Runnable
    {
        private final int i,j,offset;
        private final int[] x;
        private final double[] a,ap,p;
        private final short[] b;
        private final DoneWaiter done;

        public DoublePartitioner( double[] a, double[] ap, short[] b, double[] p, int i, int j, int offset, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.p = p;
            this.i = i;
            this.j = j;
            this.offset = offset;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int len = j-i;
                int i0,i1,i2,i3,i4,i5,i6,i7;
                int i8,i9,iA,iB,iC,iD,iE,iF;
                int n,np;
                double x0,x1,x2,x3,x4,x5,x6,x7;
                double x8,x9,xA,xB,xC,xD,xE,xF;
                int ii=i, jj=i-offset,count=len;
                for( ; count>=16 ; count-=16 )
                {
                    x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
                    x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
                    x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
                    xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
                    ii += 16;
                    n = p.length;
                    i0=0; i1=0; i2=0; i3=0; i4=0; i5=0; i6=0; i7=0;
                    i8=0; i9=0; iA=0; iB=0; iC=0; iD=0; iE=0; iF=0;
                    while( n!=1 )
                    {
                        // | <xK | ?? | >=xK |
                        //        ^    ^
                        //        iK   iK+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                        i1 += p[i1+n]<x1?np:0;
                        i2 += p[i2+n]<x2?np:0;
                        i3 += p[i3+n]<x3?np:0;
                        i4 += p[i4+n]<x4?np:0;
                        i5 += p[i5+n]<x5?np:0;
                        i6 += p[i6+n]<x6?np:0;
                        i7 += p[i7+n]<x7?np:0;
                        i8 += p[i8+n]<x8?np:0;
                        i9 += p[i9+n]<x9?np:0;
                        iA += p[iA+n]<xA?np:0;
                        iB += p[iB+n]<xB?np:0;
                        iC += p[iC+n]<xC?np:0;
                        iD += p[iD+n]<xD?np:0;
                        iE += p[iE+n]<xE?np:0;
                        iF += p[iF+n]<xF?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    i1 += p[i1]<=x1?1:0;
                    i2 += p[i2]<=x2?1:0;
                    i3 += p[i3]<=x3?1:0;
                    i4 += p[i4]<=x4?1:0;
                    i5 += p[i5]<=x5?1:0;
                    i6 += p[i6]<=x6?1:0;
                    i7 += p[i7]<=x7?1:0;
                    i8 += p[i8]<=x8?1:0;
                    i9 += p[i9]<=x9?1:0;
                    iA += p[iA]<=xA?1:0;
                    iB += p[iB]<=xB?1:0;
                    iC += p[iC]<=xC?1:0;
                    iD += p[iD]<=xD?1:0;
                    iE += p[iE]<=xE?1:0;
                    iF += p[iF]<=xF?1:0;
                    b[jj+0] = (short)i0;
                    x[i0]++;
                    b[jj+1] = (short)i1;
                    x[i1]++;
                    b[jj+2] = (short)i2;
                    x[i2]++;
                    b[jj+3] = (short)i3;
                    x[i3]++;
                    b[jj+4] = (short)i4;
                    x[i4]++;
                    b[jj+5] = (short)i5;
                    x[i5]++;
                    b[jj+6] = (short)i6;
                    x[i6]++;
                    b[jj+7] = (short)i7;
                    x[i7]++;
                    b[jj+8] = (short)i8;
                    x[i8]++;
                    b[jj+9] = (short)i9;
                    x[i9]++;
                    b[jj+10] = (short)iA;
                    x[iA]++;
                    b[jj+11] = (short)iB;
                    x[iB]++;
                    b[jj+12] = (short)iC;
                    x[iC]++;
                    b[jj+13] = (short)iD;
                    x[iD]++;
                    b[jj+14] = (short)iE;
                    x[iE]++;
                    b[jj+15] = (short)iF;
                    x[iF]++;
                    jj += 16;
                }
                while( count-- != 0 )
                {
                    i0=0;
                    x0=a[ii++];
                    n = p.length;
                    while( n!=1 )
                    {
                        // | <x | ?? | >=x |
                        //       ^    ^
                        //       i    i+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    b[jj++] = (short)i0;
                    x[i0]++;
                }
                done.signalOneDone();
            }
            catch( ArrayIndexOutOfBoundsException e )
            {
                System.out.println("p.length="+p.length);
                e.printStackTrace();
            }
            catch( Throwable e )
            {
                e.printStackTrace();
            }
        }
    }

    static class LongPartitioner implements Runnable
    {
        private final int i,j,offset;
        private final int[] x;
        private final long[] a,ap,p;
        private final short[] b;
        private final DoneWaiter done;

        public LongPartitioner( long[] a, long[] ap, short[] b, long[] p, int i, int j, int offset, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.p = p;
            this.i = i;
            this.j = j;
            this.offset = offset;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int len = j-i;
                int i0,i1,i2,i3,i4,i5,i6,i7;
                int i8,i9,iA,iB,iC,iD,iE,iF;
                int n,np;
                long x0,x1,x2,x3,x4,x5,x6,x7;
                long x8,x9,xA,xB,xC,xD,xE,xF;
                int ii=i, jj=i-offset,count=len;
                for( ; count>=16 ; count-=16 )
                {
                    x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
                    x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
                    x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
                    xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
                    ii += 16;
                    n = p.length;
                    i0=0; i1=0; i2=0; i3=0; i4=0; i5=0; i6=0; i7=0;
                    i8=0; i9=0; iA=0; iB=0; iC=0; iD=0; iE=0; iF=0;
                    while( n!=1 )
                    {
                        // | <xK | ?? | >=xK |
                        //        ^    ^
                        //        iK   iK+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                        i1 += p[i1+n]<x1?np:0;
                        i2 += p[i2+n]<x2?np:0;
                        i3 += p[i3+n]<x3?np:0;
                        i4 += p[i4+n]<x4?np:0;
                        i5 += p[i5+n]<x5?np:0;
                        i6 += p[i6+n]<x6?np:0;
                        i7 += p[i7+n]<x7?np:0;
                        i8 += p[i8+n]<x8?np:0;
                        i9 += p[i9+n]<x9?np:0;
                        iA += p[iA+n]<xA?np:0;
                        iB += p[iB+n]<xB?np:0;
                        iC += p[iC+n]<xC?np:0;
                        iD += p[iD+n]<xD?np:0;
                        iE += p[iE+n]<xE?np:0;
                        iF += p[iF+n]<xF?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    i1 += p[i1]<=x1?1:0;
                    i2 += p[i2]<=x2?1:0;
                    i3 += p[i3]<=x3?1:0;
                    i4 += p[i4]<=x4?1:0;
                    i5 += p[i5]<=x5?1:0;
                    i6 += p[i6]<=x6?1:0;
                    i7 += p[i7]<=x7?1:0;
                    i8 += p[i8]<=x8?1:0;
                    i9 += p[i9]<=x9?1:0;
                    iA += p[iA]<=xA?1:0;
                    iB += p[iB]<=xB?1:0;
                    iC += p[iC]<=xC?1:0;
                    iD += p[iD]<=xD?1:0;
                    iE += p[iE]<=xE?1:0;
                    iF += p[iF]<=xF?1:0;
                    b[jj+0] = (short)i0;
                    x[i0]++;
                    b[jj+1] = (short)i1;
                    x[i1]++;
                    b[jj+2] = (short)i2;
                    x[i2]++;
                    b[jj+3] = (short)i3;
                    x[i3]++;
                    b[jj+4] = (short)i4;
                    x[i4]++;
                    b[jj+5] = (short)i5;
                    x[i5]++;
                    b[jj+6] = (short)i6;
                    x[i6]++;
                    b[jj+7] = (short)i7;
                    x[i7]++;
                    b[jj+8] = (short)i8;
                    x[i8]++;
                    b[jj+9] = (short)i9;
                    x[i9]++;
                    b[jj+10] = (short)iA;
                    x[iA]++;
                    b[jj+11] = (short)iB;
                    x[iB]++;
                    b[jj+12] = (short)iC;
                    x[iC]++;
                    b[jj+13] = (short)iD;
                    x[iD]++;
                    b[jj+14] = (short)iE;
                    x[iE]++;
                    b[jj+15] = (short)iF;
                    x[iF]++;
                    jj += 16;
                }
                while( count-- != 0 )
                {
                    i0=0;
                    x0=a[ii++];
                    n = p.length;
                    while( n!=1 )
                    {
                        // | <x | ?? | >=x |
                        //       ^    ^
                        //       i    i+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    b[jj++] = (short)i0;
                    x[i0]++;
                }
                done.signalOneDone();
            }
            catch( ArrayIndexOutOfBoundsException e )
            {
                System.out.println("p.length="+p.length);
                e.printStackTrace();
            }
            catch( Throwable e )
            {
                e.printStackTrace();
            }
        }
    }

    static class FloatPartitioner implements Runnable
    {
        private final int i,j,offset;
        private final int[] x;
        private final float[] a,ap,p;
        private final short[] b;
        private final DoneWaiter done;

        public FloatPartitioner( float[] a, float[] ap, short[] b, float[] p, int i, int j, int offset, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.p = p;
            this.i = i;
            this.j = j;
            this.offset = offset;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int len = j-i;
                int i0,i1,i2,i3,i4,i5,i6,i7;
                int i8,i9,iA,iB,iC,iD,iE,iF;
                int n,np;
                float x0,x1,x2,x3,x4,x5,x6,x7;
                float x8,x9,xA,xB,xC,xD,xE,xF;
                int ii=i, jj=i-offset,count=len;
                for( ; count>=16 ; count-=16 )
                {
                    x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
                    x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
                    x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
                    xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
                    ii += 16;
                    n = p.length;
                    i0=0; i1=0; i2=0; i3=0; i4=0; i5=0; i6=0; i7=0;
                    i8=0; i9=0; iA=0; iB=0; iC=0; iD=0; iE=0; iF=0;
                    while( n!=1 )
                    {
                        // | <xK | ?? | >=xK |
                        //        ^    ^
                        //        iK   iK+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                        i1 += p[i1+n]<x1?np:0;
                        i2 += p[i2+n]<x2?np:0;
                        i3 += p[i3+n]<x3?np:0;
                        i4 += p[i4+n]<x4?np:0;
                        i5 += p[i5+n]<x5?np:0;
                        i6 += p[i6+n]<x6?np:0;
                        i7 += p[i7+n]<x7?np:0;
                        i8 += p[i8+n]<x8?np:0;
                        i9 += p[i9+n]<x9?np:0;
                        iA += p[iA+n]<xA?np:0;
                        iB += p[iB+n]<xB?np:0;
                        iC += p[iC+n]<xC?np:0;
                        iD += p[iD+n]<xD?np:0;
                        iE += p[iE+n]<xE?np:0;
                        iF += p[iF+n]<xF?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    i1 += p[i1]<=x1?1:0;
                    i2 += p[i2]<=x2?1:0;
                    i3 += p[i3]<=x3?1:0;
                    i4 += p[i4]<=x4?1:0;
                    i5 += p[i5]<=x5?1:0;
                    i6 += p[i6]<=x6?1:0;
                    i7 += p[i7]<=x7?1:0;
                    i8 += p[i8]<=x8?1:0;
                    i9 += p[i9]<=x9?1:0;
                    iA += p[iA]<=xA?1:0;
                    iB += p[iB]<=xB?1:0;
                    iC += p[iC]<=xC?1:0;
                    iD += p[iD]<=xD?1:0;
                    iE += p[iE]<=xE?1:0;
                    iF += p[iF]<=xF?1:0;
                    b[jj+0] = (short)i0;
                    x[i0]++;
                    b[jj+1] = (short)i1;
                    x[i1]++;
                    b[jj+2] = (short)i2;
                    x[i2]++;
                    b[jj+3] = (short)i3;
                    x[i3]++;
                    b[jj+4] = (short)i4;
                    x[i4]++;
                    b[jj+5] = (short)i5;
                    x[i5]++;
                    b[jj+6] = (short)i6;
                    x[i6]++;
                    b[jj+7] = (short)i7;
                    x[i7]++;
                    b[jj+8] = (short)i8;
                    x[i8]++;
                    b[jj+9] = (short)i9;
                    x[i9]++;
                    b[jj+10] = (short)iA;
                    x[iA]++;
                    b[jj+11] = (short)iB;
                    x[iB]++;
                    b[jj+12] = (short)iC;
                    x[iC]++;
                    b[jj+13] = (short)iD;
                    x[iD]++;
                    b[jj+14] = (short)iE;
                    x[iE]++;
                    b[jj+15] = (short)iF;
                    x[iF]++;
                    jj += 16;
                }
                while( count-- != 0 )
                {
                    i0=0;
                    x0=a[ii++];
                    n = p.length;
                    while( n!=1 )
                    {
                        // | <x | ?? | >=x |
                        //       ^    ^
                        //       i    i+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    b[jj++] = (short)i0;
                    x[i0]++;
                }
                done.signalOneDone();
            }
            catch( ArrayIndexOutOfBoundsException e )
            {
                System.out.println("p.length="+p.length);
                e.printStackTrace();
            }
            catch( Throwable e )
            {
                e.printStackTrace();
            }
        }
    }

    static class IntPartitioner implements Runnable
    {
        private final int i,j,offset;
        private final int[] x;
        private final int[] a,ap,p;
        private final short[] b;
        private final DoneWaiter done;

        public IntPartitioner( int[] a, int[] ap, short[] b, int[] p, int i, int j, int offset, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.p = p;
            this.i = i;
            this.j = j;
            this.offset = offset;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int len = j-i;
                int i0,i1,i2,i3,i4,i5,i6,i7;
                int i8,i9,iA,iB,iC,iD,iE,iF;
                int n,np;
                int x0,x1,x2,x3,x4,x5,x6,x7;
                int x8,x9,xA,xB,xC,xD,xE,xF;
                int ii=i, jj=i-offset,count=len;
                for( ; count>=16 ; count-=16 )
                {
                    x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
                    x4=a[ii+4]; x5=a[ii+5]; x6=a[ii+6]; x7=a[ii+7];
                    x8=a[ii+8]; x9=a[ii+9]; xA=a[ii+10]; xB=a[ii+11];
                    xC=a[ii+12]; xD=a[ii+13]; xE=a[ii+14]; xF=a[ii+15];
                    ii += 16;
                    n = p.length;
                    i0=0; i1=0; i2=0; i3=0; i4=0; i5=0; i6=0; i7=0;
                    i8=0; i9=0; iA=0; iB=0; iC=0; iD=0; iE=0; iF=0;
                    while( n!=1 )
                    {
                        // | <xK | ?? | >=xK |
                        //        ^    ^
                        //        iK   iK+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                        i1 += p[i1+n]<x1?np:0;
                        i2 += p[i2+n]<x2?np:0;
                        i3 += p[i3+n]<x3?np:0;
                        i4 += p[i4+n]<x4?np:0;
                        i5 += p[i5+n]<x5?np:0;
                        i6 += p[i6+n]<x6?np:0;
                        i7 += p[i7+n]<x7?np:0;
                        i8 += p[i8+n]<x8?np:0;
                        i9 += p[i9+n]<x9?np:0;
                        iA += p[iA+n]<xA?np:0;
                        iB += p[iB+n]<xB?np:0;
                        iC += p[iC+n]<xC?np:0;
                        iD += p[iD+n]<xD?np:0;
                        iE += p[iE+n]<xE?np:0;
                        iF += p[iF+n]<xF?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    i1 += p[i1]<=x1?1:0;
                    i2 += p[i2]<=x2?1:0;
                    i3 += p[i3]<=x3?1:0;
                    i4 += p[i4]<=x4?1:0;
                    i5 += p[i5]<=x5?1:0;
                    i6 += p[i6]<=x6?1:0;
                    i7 += p[i7]<=x7?1:0;
                    i8 += p[i8]<=x8?1:0;
                    i9 += p[i9]<=x9?1:0;
                    iA += p[iA]<=xA?1:0;
                    iB += p[iB]<=xB?1:0;
                    iC += p[iC]<=xC?1:0;
                    iD += p[iD]<=xD?1:0;
                    iE += p[iE]<=xE?1:0;
                    iF += p[iF]<=xF?1:0;
                    b[jj+0] = (short)i0;
                    x[i0]++;
                    b[jj+1] = (short)i1;
                    x[i1]++;
                    b[jj+2] = (short)i2;
                    x[i2]++;
                    b[jj+3] = (short)i3;
                    x[i3]++;
                    b[jj+4] = (short)i4;
                    x[i4]++;
                    b[jj+5] = (short)i5;
                    x[i5]++;
                    b[jj+6] = (short)i6;
                    x[i6]++;
                    b[jj+7] = (short)i7;
                    x[i7]++;
                    b[jj+8] = (short)i8;
                    x[i8]++;
                    b[jj+9] = (short)i9;
                    x[i9]++;
                    b[jj+10] = (short)iA;
                    x[iA]++;
                    b[jj+11] = (short)iB;
                    x[iB]++;
                    b[jj+12] = (short)iC;
                    x[iC]++;
                    b[jj+13] = (short)iD;
                    x[iD]++;
                    b[jj+14] = (short)iE;
                    x[iE]++;
                    b[jj+15] = (short)iF;
                    x[iF]++;
                    jj += 16;
                }
                while( count-- != 0 )
                {
                    i0=0;
                    x0=a[ii++];
                    n = p.length;
                    while( n!=1 )
                    {
                        // | <x | ?? | >=x |
                        //       ^    ^
                        //       i    i+n
                        // n>0 is of form 2^k-1
                        n >>= 1;
                        np = n+1;
                        i0 += p[i0+n]<x0?np:0;
                    }
                    i0 += p[i0]<=x0?1:0;
                    b[jj++] = (short)i0;
                    x[i0]++;
                }
                done.signalOneDone();
            }
            catch( ArrayIndexOutOfBoundsException e )
            {
                System.out.println("p.length="+p.length);
                e.printStackTrace();
            }
            catch( Throwable e )
            {
                e.printStackTrace();
            }
        }
    }

    static class EPartitioner<E extends Comparable<? super E>> implements Runnable
    {
        private final int i,j,offset;
        private final int[] x;
        private final E[] a,ap,p;
        private final short[] b;
        private final DoneWaiter done;
        private final int pivcount;

        // pivcount is one of 31, 63, 127, ..., 32767
        public EPartitioner( E[] a, E[] ap, short[] b, E[] p, int i, int j, int offset, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.p = p;
            this.i = i;
            this.j = j;
            this.offset = offset;
            this.x = x;
            this.done = done;
            this.pivcount = p.length;
        }

        public void run()
        {
            int len = j-i;
            int i0,i1,i2,i3;
            int n,np;
            E x0,x1,x2,x3;
            int ii=i, jj=i-offset,count=len;
            for( ; count>=4 ; count-=4 )
            {
                i0=0; i1=0; i2=0; i3=0;
                x0=a[ii+0]; x1=a[ii+1]; x2=a[ii+2]; x3=a[ii+3];
                ii += 4;
                n = pivcount;
                while( n!=1 )
                {
                    // | <x | ?? | >=x |
                    //       ^    ^
                    //       i    i+n
                    // n>0 is of form 2^k-1
                    n >>= 1;
                    np = n+1;
                    i0 += p[i0+n].compareTo(x0)<0?np:0;
                    i1 += p[i1+n].compareTo(x1)<0?np:0;
                    i2 += p[i2+n].compareTo(x2)<0?np:0;
                    i3 += p[i3+n].compareTo(x3)<0?np:0;
                }
                i0 += p[i0].compareTo(x0)<=0?1:0;
                i1 += p[i1].compareTo(x1)<=0?1:0;
                i2 += p[i2].compareTo(x2)<=0?1:0;
                i3 += p[i3].compareTo(x3)<=0?1:0;
                b[jj+0] = (short)i0;
                b[jj+1] = (short)i1;
                b[jj+2] = (short)i2;
                b[jj+3] = (short)i3;
                x[i0]++;
                x[i1]++;
                x[i2]++;
                x[i3]++;
                jj += 4;
            }
            for( ; count!=0 ; count-- )
            {
                i0=0;
                x0=a[ii++];
                n = pivcount;
                while( n!=1 )
                {
                    // | <x | ?? | >=x |
                    //       ^    ^
                    //       i    i+n
                    // n>0 is of form 2^k-1
                    n >>= 1;
                    np = n+1;
                    i0 += p[i0+n].compareTo(x0)<0?np:0;
                }
                i0 += p[i0].compareTo(x0)<=0?1:0;
                b[jj++] = (short)i0;
                x[i0]++;
            }
            done.signalOneDone();
        }
    }

    static class DoubleCopier implements Runnable
    {
        private final int offset, start, len;
        private final double[] a,ap;
        private final short[] b;
        private final int[] x;
        private final DoneWaiter done;

        public DoubleCopier( double[] a, double[] ap, short[] b, int offset, int start, int len, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.offset = offset;
            this.start = start;
            this.len = len;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int count = len;
                int ii = start;
                while( count >= 16 )
                {
                    count -= 16;
                    ap[x[b[ii+0]]++] = a[ii+offset+0];
                    ap[x[b[ii+1]]++] = a[ii+offset+1];
                    ap[x[b[ii+2]]++] = a[ii+offset+2];
                    ap[x[b[ii+3]]++] = a[ii+offset+3];
                    ap[x[b[ii+4]]++] = a[ii+offset+4];
                    ap[x[b[ii+5]]++] = a[ii+offset+5];
                    ap[x[b[ii+6]]++] = a[ii+offset+6];
                    ap[x[b[ii+7]]++] = a[ii+offset+7];
                    ap[x[b[ii+8]]++] = a[ii+offset+8];
                    ap[x[b[ii+9]]++] = a[ii+offset+9];
                    ap[x[b[ii+10]]++] = a[ii+offset+10];
                    ap[x[b[ii+11]]++] = a[ii+offset+11];
                    ap[x[b[ii+12]]++] = a[ii+offset+12];
                    ap[x[b[ii+13]]++] = a[ii+offset+13];
                    ap[x[b[ii+14]]++] = a[ii+offset+14];
                    ap[x[b[ii+15]]++] = a[ii+offset+15];
                    ii += 16;
                }
                while( count != 0 )
                {
                    count--;
                    ap[x[b[ii]]++] = a[ii+offset];
                    ii++;
                }
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.out.println("offset,start,len = "+offset+","+start+","+len);
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class LongCopier implements Runnable
    {
        private final int offset, start, len;
        private final long[] a,ap;
        private final short[] b;
        private final int[] x;
        private final DoneWaiter done;

        public LongCopier( long[] a, long[] ap, short[] b, int offset, int start, int len, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.offset = offset;
            this.start = start;
            this.len = len;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int count = len;
                int ii = start;
                while( count >= 16 )
                {
                    count -= 16;
                    ap[x[b[ii+0]]++] = a[ii+offset+0];
                    ap[x[b[ii+1]]++] = a[ii+offset+1];
                    ap[x[b[ii+2]]++] = a[ii+offset+2];
                    ap[x[b[ii+3]]++] = a[ii+offset+3];
                    ap[x[b[ii+4]]++] = a[ii+offset+4];
                    ap[x[b[ii+5]]++] = a[ii+offset+5];
                    ap[x[b[ii+6]]++] = a[ii+offset+6];
                    ap[x[b[ii+7]]++] = a[ii+offset+7];
                    ap[x[b[ii+8]]++] = a[ii+offset+8];
                    ap[x[b[ii+9]]++] = a[ii+offset+9];
                    ap[x[b[ii+10]]++] = a[ii+offset+10];
                    ap[x[b[ii+11]]++] = a[ii+offset+11];
                    ap[x[b[ii+12]]++] = a[ii+offset+12];
                    ap[x[b[ii+13]]++] = a[ii+offset+13];
                    ap[x[b[ii+14]]++] = a[ii+offset+14];
                    ap[x[b[ii+15]]++] = a[ii+offset+15];
                    ii += 16;
                }
                while( count != 0 )
                {
                    count--;
                    ap[x[b[ii]]++] = a[ii+offset];
                    ii++;
                }
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.out.println("offset,start,len = "+offset+","+start+","+len);
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class FloatCopier implements Runnable
    {
        private final int offset, start, len;
        private final float[] a,ap;
        private final short[] b;
        private final int[] x;
        private final DoneWaiter done;

        public FloatCopier( float[] a, float[] ap, short[] b, int offset, int start, int len, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.offset = offset;
            this.start = start;
            this.len = len;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int count = len;
                int ii = start;
                while( count >= 16 )
                {
                    count -= 16;
                    ap[x[b[ii+0]]++] = a[ii+offset+0];
                    ap[x[b[ii+1]]++] = a[ii+offset+1];
                    ap[x[b[ii+2]]++] = a[ii+offset+2];
                    ap[x[b[ii+3]]++] = a[ii+offset+3];
                    ap[x[b[ii+4]]++] = a[ii+offset+4];
                    ap[x[b[ii+5]]++] = a[ii+offset+5];
                    ap[x[b[ii+6]]++] = a[ii+offset+6];
                    ap[x[b[ii+7]]++] = a[ii+offset+7];
                    ap[x[b[ii+8]]++] = a[ii+offset+8];
                    ap[x[b[ii+9]]++] = a[ii+offset+9];
                    ap[x[b[ii+10]]++] = a[ii+offset+10];
                    ap[x[b[ii+11]]++] = a[ii+offset+11];
                    ap[x[b[ii+12]]++] = a[ii+offset+12];
                    ap[x[b[ii+13]]++] = a[ii+offset+13];
                    ap[x[b[ii+14]]++] = a[ii+offset+14];
                    ap[x[b[ii+15]]++] = a[ii+offset+15];
                    ii += 16;
                }
                while( count != 0 )
                {
                    count--;
                    ap[x[b[ii]]++] = a[ii+offset];
                    ii++;
                }
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.out.println("offset,start,len = "+offset+","+start+","+len);
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class IntCopier implements Runnable
    {
        private final int offset, start, len;
        private final int[] a,ap;
        private final short[] b;
        private final int[] x;
        private final DoneWaiter done;

        public IntCopier( int[] a, int[] ap, short[] b, int offset, int start, int len, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.offset = offset;
            this.start = start;
            this.len = len;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int count = len;
                int ii = start;
                while( count >= 16 )
                {
                    count -= 16;
                    ap[x[b[ii+0]]++] = a[ii+offset+0];
                    ap[x[b[ii+1]]++] = a[ii+offset+1];
                    ap[x[b[ii+2]]++] = a[ii+offset+2];
                    ap[x[b[ii+3]]++] = a[ii+offset+3];
                    ap[x[b[ii+4]]++] = a[ii+offset+4];
                    ap[x[b[ii+5]]++] = a[ii+offset+5];
                    ap[x[b[ii+6]]++] = a[ii+offset+6];
                    ap[x[b[ii+7]]++] = a[ii+offset+7];
                    ap[x[b[ii+8]]++] = a[ii+offset+8];
                    ap[x[b[ii+9]]++] = a[ii+offset+9];
                    ap[x[b[ii+10]]++] = a[ii+offset+10];
                    ap[x[b[ii+11]]++] = a[ii+offset+11];
                    ap[x[b[ii+12]]++] = a[ii+offset+12];
                    ap[x[b[ii+13]]++] = a[ii+offset+13];
                    ap[x[b[ii+14]]++] = a[ii+offset+14];
                    ap[x[b[ii+15]]++] = a[ii+offset+15];
                    ii += 16;
                }
                while( count != 0 )
                {
                    count--;
                    ap[x[b[ii]]++] = a[ii+offset];
                    ii++;
                }
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.out.println("offset,start,len = "+offset+","+start+","+len);
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class ECopier<E extends Comparable<? super E>> implements Runnable
    {
        private final int offset, start, len;
        private final E[] a,ap;
        private final short[] b;
        private final int[] x;
        private final DoneWaiter done;

        public ECopier( E[] a, E[] ap, short[] b, int offset, int start, int len, int[] x, DoneWaiter done )
        {
            this.a = a;
            this.ap = ap;
            this.b = b;
            this.offset = offset;
            this.start = start;
            this.len = len;
            this.x = x;
            this.done = done;
        }

        public void run()
        {
            try
            {
                int count = len;
                int ii = start;
                while( count >= 8 )
                {
                    count -= 8;
                    ap[x[b[ii+0]]++] = a[ii+offset+0];
                    ap[x[b[ii+1]]++] = a[ii+offset+1];
                    ap[x[b[ii+2]]++] = a[ii+offset+2];
                    ap[x[b[ii+3]]++] = a[ii+offset+3];
                    ap[x[b[ii+4]]++] = a[ii+offset+4];
                    ap[x[b[ii+5]]++] = a[ii+offset+5];
                    ap[x[b[ii+6]]++] = a[ii+offset+6];
                    ap[x[b[ii+7]]++] = a[ii+offset+7];
                    ii += 8;
                }
                while( count != 0 )
                {
                    count--;
                    ap[x[b[ii]]++] = a[ii+offset];
                    ii++;
                }
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.out.println("offset,start,len = "+offset+","+start+","+len);
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class DoubleSorter implements Runnable
    {
        private final double[] a,ap;
        private final short[] b;
        private final int apos, appos, len;
        private final boolean copy;
        private final DoneWaiter done;

        public DoubleSorter( double[] a, int apos, double[] ap, int appos, short[] b, int len, boolean copy, DoneWaiter done )
        {
            this.a = a;
            this.apos = apos;
            this.ap = ap;
            this.appos = appos;
            this.b = b;
            this.len = len;
            this.copy = copy;
            this.done = done;
        }

        public void run()
        {
            try
            {
                if( copy )
                    System.arraycopy(ap,appos,a,apos,len);
                else
                    lowSort(ap,appos,a,apos,b,len,false);
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class LongSorter implements Runnable
    {
        private final long[] a,ap;
        private final short[] b;
        private final int apos, appos, len;
        private final boolean copy;
        private final DoneWaiter done;

        public LongSorter( long[] a, int apos, long[] ap, int appos, short[] b, int len, boolean copy, DoneWaiter done )
        {
            this.a = a;
            this.apos = apos;
            this.ap = ap;
            this.appos = appos;
            this.b = b;
            this.len = len;
            this.copy = copy;
            this.done = done;
        }

        public void run()
        {
            try
            {
                if( copy )
                    System.arraycopy(ap,appos,a,apos,len);
                else
                    lowSort(ap,appos,a,apos,b,len,false);
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class FloatSorter implements Runnable
    {
        private final float[] a,ap;
        private final short[] b;
        private final int apos, appos, len;
        private final boolean copy;
        private final DoneWaiter done;

        public FloatSorter( float[] a, int apos, float[] ap, int appos, short[] b, int len, boolean copy, DoneWaiter done )
        {
            this.a = a;
            this.apos = apos;
            this.ap = ap;
            this.appos = appos;
            this.b = b;
            this.len = len;
            this.copy = copy;
            this.done = done;
        }

        public void run()
        {
            try
            {
                if( copy )
                    System.arraycopy(ap,appos,a,apos,len);
                else
                    lowSort(ap,appos,a,apos,b,len,false);
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class IntSorter implements Runnable
    {
        private final int[] a,ap;
        private final short[] b;
        private final int apos, appos, len;
        private final boolean copy;
        private final DoneWaiter done;

        public IntSorter( int[] a, int apos, int[] ap, int appos, short[] b, int len, boolean copy, DoneWaiter done )
        {
            this.a = a;
            this.apos = apos;
            this.ap = ap;
            this.appos = appos;
            this.b = b;
            this.len = len;
            this.copy = copy;
            this.done = done;
        }

        public void run()
        {
            try
            {
                if( copy )
                    System.arraycopy(ap,appos,a,apos,len);
                else
                    lowSort(ap,appos,a,apos,b,len,false);
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    static class ESorter<E extends Comparable<? super E>> implements Runnable
    {
        private final E[] a,ap;
        private final short[] b;
        private final int apos, appos, len;
        private final boolean copy;
        private final DoneWaiter done;

        public ESorter( E[] a, int apos, E[] ap, int appos, short[] b, int len, boolean copy, DoneWaiter done )
        {
            this.a = a;
            this.apos = apos;
            this.ap = ap;
            this.appos = appos;
            this.b = b;
            this.len = len;
            this.copy = copy;
            this.done = done;
        }

        public void run()
        {
            try
            {
                if( copy )
                    System.arraycopy(ap,appos,a,apos,len);
                else
                    lowSort(ap,appos,a,apos,b,len,false);
            }
            catch( Throwable e )
            {
                e.printStackTrace();
                System.exit(1);
            }
            done.signalOneDone();
        }
    }

    public static void parallelSort( ExecutorService e, int t, double[] a, int i, int j )
    {
        final int len = j-i;
        if( len < PARALLELCUTOFF_DOUBLE )
        {
            serialSort(a,i,j);
            return;
        }
        double[] p = extractPivots(a,i,j,t);
        if( p==null )
        {
            serialSort(a,i,j);
            return;
        }
        final int pivcount = p.length;
        final int segmentcount = pivcount+1;
        final int taskcount = 2*t;
        double[] ap = new double[len];
        short[] b = new short[len];
        int[][] xx = new int[taskcount][segmentcount];
        DoneWaiter done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            e.submit(new DoublePartitioner(a,ap,b,p,i+(int)(k*(j-i)/taskcount),i+(int)((k+1)*(j-i)/taskcount),i,xx[(int)k],done));
        }
        int[] x = new int[segmentcount];
        done.waitUntilAllDone();
        int tmp, pos=0;
        for( int r=0 ; r!=segmentcount ; r++ )
        {
            for( int s=0 ; s!=taskcount ; s++ )
            {
                tmp = xx[s][r];
                xx[s][r] = pos;
                pos += tmp;
            }
            x[r] += pos;
        }
        done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            int from = (int)(k*(j-i)/taskcount);
            int to = (int)((k+1)*(j-i)/taskcount);
            e.submit(new DoubleCopier(a,ap,b,i,from,to-from,xx[(int)k],done));
        }
        done.waitUntilAllDone();
        done = new DoneWaiter(segmentcount);
        e.submit(new DoubleSorter(a,i,ap,0,b,x[0],false,done));
        for( int k=0 ; k!=pivcount-1 ; k++ )
        {
            e.submit(new DoubleSorter(a,i+x[k],ap,x[k],b,x[k+1]-x[k],p[k]==p[k+1],done));
        }
        e.submit(new DoubleSorter(a,i+x[pivcount-1],ap,x[pivcount-1],b,x[pivcount]-x[pivcount-1],false,done));
        done.waitUntilAllDone();
    }

    public static void parallelSort( ExecutorService e, int t, long[] a, int i, int j )
    {
        final int len = j-i;
        if( len < PARALLELCUTOFF_LONG )
        {
            serialSort(a,i,j);
            return;
        }
        long[] p = extractPivots(a,i,j,t);
        if( p==null )
        {
            serialSort(a,i,j);
            return;
        }
        final int pivcount = p.length;
        final int segmentcount = pivcount+1;
        final int taskcount = 2*t;
        long[] ap = new long[len];
        short[] b = new short[len];
        int[][] xx = new int[taskcount][segmentcount];
        DoneWaiter done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            e.submit(new LongPartitioner(a,ap,b,p,i+(int)(k*(j-i)/taskcount),i+(int)((k+1)*(j-i)/taskcount),i,xx[(int)k],done));
        }
        int[] x = new int[segmentcount];
        done.waitUntilAllDone();
        int tmp, pos=0;
        for( int r=0 ; r!=segmentcount ; r++ )
        {
            for( int s=0 ; s!=taskcount ; s++ )
            {
                tmp = xx[s][r];
                xx[s][r] = pos;
                pos += tmp;
            }
            x[r] += pos;
        }
        done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            int from = (int)(k*(j-i)/taskcount);
            int to = (int)((k+1)*(j-i)/taskcount);
            e.submit(new LongCopier(a,ap,b,i,from,to-from,xx[(int)k],done));
        }
        done.waitUntilAllDone();
        done = new DoneWaiter(segmentcount);
        e.submit(new LongSorter(a,i,ap,0,b,x[0],false,done));
        for( int k=0 ; k!=pivcount-1 ; k++ )
        {
            e.submit(new LongSorter(a,i+x[k],ap,x[k],b,x[k+1]-x[k],p[k]==p[k+1],done));
        }
        e.submit(new LongSorter(a,i+x[pivcount-1],ap,x[pivcount-1],b,x[pivcount]-x[pivcount-1],false,done));
        done.waitUntilAllDone();
    }

    public static void parallelSort( ExecutorService e, int t, float[] a, int i, int j )
    {
        final int len = j-i;
        if( len < PARALLELCUTOFF_FLOAT )
        {
            serialSort(a,i,j);
            return;
        }
        float[] p = extractPivots(a,i,j,t);
        if( p==null )
        {
            serialSort(a,i,j);
            return;
        }
        final int pivcount = p.length;
        final int segmentcount = pivcount+1;
        final int taskcount = 2*t;
        float[] ap = new float[len];
        short[] b = new short[len];
        int[][] xx = new int[taskcount][segmentcount];
        DoneWaiter done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            e.submit(new FloatPartitioner(a,ap,b,p,i+(int)(k*(j-i)/taskcount),i+(int)((k+1)*(j-i)/taskcount),i,xx[(int)k],done));
        }
        int[] x = new int[segmentcount];
        done.waitUntilAllDone();
        int tmp, pos=0;
        for( int r=0 ; r!=segmentcount ; r++ )
        {
            for( int s=0 ; s!=taskcount ; s++ )
            {
                tmp = xx[s][r];
                xx[s][r] = pos;
                pos += tmp;
            }
            x[r] += pos;
        }
        done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            int from = (int)(k*(j-i)/taskcount);
            int to = (int)((k+1)*(j-i)/taskcount);
            e.submit(new FloatCopier(a,ap,b,i,from,to-from,xx[(int)k],done));
        }
        done.waitUntilAllDone();
        done = new DoneWaiter(segmentcount);
        e.submit(new FloatSorter(a,i,ap,0,b,x[0],false,done));
        for( int k=0 ; k!=pivcount-1 ; k++ )
        {
            e.submit(new FloatSorter(a,i+x[k],ap,x[k],b,x[k+1]-x[k],false,done));
        }
        e.submit(new FloatSorter(a,i+x[pivcount-1],ap,x[pivcount-1],b,x[pivcount]-x[pivcount-1],false,done));
        done.waitUntilAllDone();
    }

    public static void parallelSort( ExecutorService e, int t, int[] a, int i, int j )
    {
        final int len = j-i;
        if( len < PARALLELCUTOFF_INT )
        {
            serialSort(a,i,j);
            return;
        }
        int[] p = extractPivots(a,i,j,t);
        if( p==null )
        {
            serialSort(a,i,j);
            return;
        }
        final int pivcount = p.length;
        final int segmentcount = pivcount+1;
        final int taskcount = 2*t;
        int[] ap = new int[len];
        short[] b = new short[len];
        int[][] xx = new int[taskcount][segmentcount];
        DoneWaiter done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            e.submit(new IntPartitioner(a,ap,b,p,i+(int)(k*(j-i)/taskcount),i+(int)((k+1)*(j-i)/taskcount),i,xx[(int)k],done));
        }
        int[] x = new int[segmentcount];
        done.waitUntilAllDone();
        int tmp, pos=0;
        for( int r=0 ; r!=segmentcount ; r++ )
        {
            for( int s=0 ; s!=taskcount ; s++ )
            {
                tmp = xx[s][r];
                xx[s][r] = pos;
                pos += tmp;
            }
            x[r] += pos;
        }
        done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            int from = (int)(k*(j-i)/taskcount);
            int to = (int)((k+1)*(j-i)/taskcount);
            e.submit(new IntCopier(a,ap,b,i,from,to-from,xx[(int)k],done));
        }
        done.waitUntilAllDone();
        done = new DoneWaiter(segmentcount);
        e.submit(new IntSorter(a,i,ap,0,b,x[0],false,done));
        for( int k=0 ; k!=pivcount-1 ; k++ )
        {
            e.submit(new IntSorter(a,i+x[k],ap,x[k],b,x[k+1]-x[k],p[k]==p[k+1],done));
        }
        e.submit(new IntSorter(a,i+x[pivcount-1],ap,x[pivcount-1],b,x[pivcount]-x[pivcount-1],false,done));
        done.waitUntilAllDone();
    }

    public static<E extends Comparable<? super E>> void parallelSort( ExecutorService e, int t, E[] a, int i, int j )
    {
        int len = j-i;
        if( len < PARALLELCUTOFF_OBJECT )
        {
            serialSort(a,i,j);
            return;
        }
        E[] p = extractPivots(a,i,j,t);
        if( p==null )
        {
            serialSort(a,i,j);
            return;
        }
        final int pivcount = p.length;
        final int taskcount = t<32 ? 4*t : t;
        E[] ap = (E[])new Comparable<?>[len];
        short[] b = new short[len];
        final int segmentcount = pivcount+1;
        int[][] xx = new int[taskcount][segmentcount];
        DoneWaiter done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            e.submit(new EPartitioner(a,ap,b,p,i+(int)(k*(j-i)/taskcount),i+(int)((k+1)*(j-i)/taskcount),i,xx[(int)k],done));
        }
        int[] x = new int[segmentcount];
        done.waitUntilAllDone();
        int tmp, pos=0;
        for( int r=0 ; r!=segmentcount ; r++ )
        {
            for( int s=0 ; s!=taskcount ; s++ )
            {
                tmp = xx[s][r];
                xx[s][r] = pos;
                pos += tmp;
            }
            x[r] += pos;
        }
        done = new DoneWaiter(taskcount);
        for( long k=0 ; k!=taskcount ; k++ )
        {
            int from = (int)(k*(j-i)/taskcount);
            int to = (int)((k+1)*(j-i)/taskcount);
            e.submit(new ECopier(a,ap,b,i,from,to-from,xx[(int)k],done));
        }
        done.waitUntilAllDone();
        done = new DoneWaiter(segmentcount);
        e.submit(new ESorter(a,i,ap,0,b,x[0],false,done));
        for( int k=0 ; k!=pivcount-1 ; k++ )
        {
            e.submit(new ESorter(a,i+x[k],ap,x[k],b,x[k+1]-x[k],p[k].compareTo(p[k+1])==0,done));
        }
        e.submit(new ESorter(a,i+x[pivcount-1],ap,x[pivcount-1],b,x[pivcount]-x[pivcount-1],false,done));
        done.waitUntilAllDone();
    }

    private static ExecutorService executor = null;

    public static ExecutorService getExecutorService()
    {
        if( executor!=null ) return executor;
        executor =
            Executors.newFixedThreadPool
                ( THREADS
                , new java.util.concurrent.ThreadFactory()
                    {
                        public Thread newThread( Runnable r )
                        {
                            Thread t = Executors.defaultThreadFactory().newThread(r);
                            t.setDaemon(true);
                            return t;
                        }
                    }
                );
        return executor;
    }

    public static void parallelSort( double[] a, int i, int j )
    {
        parallelSort(getExecutorService(),THREADS,a,i,j);
    }

    public static void parallelSort( long[] a, int i, int j )
    {
        parallelSort(getExecutorService(),THREADS,a,i,j);
    }

    public static void parallelSort( float[] a, int i, int j )
    {
        parallelSort(getExecutorService(),THREADS,a,i,j);
    }

    public static void parallelSort( int[] a, int i, int j )
    {
        parallelSort(getExecutorService(),THREADS,a,i,j);
    }

    public static<E extends Comparable<? super E>> void parallelSort( E[] a, int i, int j )
    {
        parallelSort(getExecutorService(),THREADS,a,i,j);
    }

    public static void parallelSort( double[] a )
    {
        parallelSort(a,0,a.length);
    }

    public static void parallelSort( long[] a )
    {
        parallelSort(a,0,a.length);
    }

    public static void parallelSort( float[] a )
    {
        parallelSort(a,0,a.length);
    }

    public static void parallelSort( int[] a )
    {
        parallelSort(a,0,a.length);
    }

    public static<E extends Comparable<? super E>> void parallelSort( E[] a )
    {
        parallelSort(a,0,a.length);
    }

    public static void sort( double[] a )
    {
        parallelSort(a);
    }

    public static void sort( float[] a )
    {
        parallelSort(a);
    }

    public static void sort( int[] a )
    {
        parallelSort(a);
    }

    public static void sort( double[] a, int i, int j )
    {
        parallelSort(a,i,j);
    }

    public static void sort( float[] a, int i, int j )
    {
        parallelSort(a,i,j);
    }

    public static void sort( int[] a, int i, int j )
    {
        parallelSort(a,i,j);
    }

    public static<E extends Comparable<? super E>> void sort( E[] a )
    {
        parallelSort(a);
    }

    public static<E extends Comparable<? super E>> void sort( E[] a, int i, int j )
    {
        parallelSort(a,i,j);
    }

    // Borrowed from http://introcs.cs.princeton.edu/java/91float/Gamma.java.html
    private static double logGamma(double x)
    {
        double tmp = (x - 0.5) * Math.log(x + 4.5) - (x + 4.5);
        double ser = 1.0 + 76.18009173    / (x + 0)   - 86.50532033    / (x + 1)
                       + 24.01409822    / (x + 2)   -  1.231739516   / (x + 3)
                       +  0.00120858003 / (x + 4)   -  0.00000536382 / (x + 5);
        return tmp + Math.log(ser * Math.sqrt(2 * Math.PI));
    }
    
    private static double entropy( int n )
    {
        return logGamma(1.0+n)/Math.log(2.0);
    }

    private static void verify( double[] a, double[] ap )
    {
        for( int i=0 ; i!=a.length ; i++ )
            if( a[i]!=ap[i] ) throw new Error("At "+i+": "+a[i]+"!="+ap[i]);
    }

    private static void verify( double[] a, int i, int j )
    {
        for( int k=i+1 ; k<j ; k++ )
            if( a[k-1]>a[k] ) throw new Error("Error at "+(k-1)+"-"+k+" "+a[k-1]+" "+a[k]);
    }

    private static void verify( double[] a )
    {
        verify(a,0,a.length);
    }

    private static void verify( long[] a, long[] ap )
    {
        for( int i=0 ; i!=a.length ; i++ )
            if( a[i]!=ap[i] ) throw new Error("At "+i+": "+a[i]+"!="+ap[i]);
    }

    private static void verify( long[] a, int i, int j )
    {
        for( int k=i+1 ; k<j ; k++ )
            if( a[k-1]>a[k] ) throw new Error("Error at "+(k-1)+"-"+k+" "+a[k-1]+" "+a[k]);
    }

    private static void verify( long[] a )
    {
        verify(a,0,a.length);
    }

    private static<E extends Comparable<? super E>> void verify( E[] a, E[] ap )
    {
        for( int i=0 ; i!=a.length ; i++ )
            if( !a[i].equals(ap[i]) ) throw new Error("At "+i+": "+a[i]+"!="+ap[i]);
    }

    private static<E extends Comparable<? super E>> void verify( E[] a, int i, int j )
    {
        for( int k=i+1 ; k<j ; k++ )
            if( a[k-1].compareTo(a[k])>0 ) throw new Error("Error at "+(k-1)+"-"+k+" "+a[k-1]+" "+a[k]);
    }

    private static<E extends Comparable<? super E>> void verify( E[] a )
    {
        verify(a,0,a.length);
    }

    private static void swap( Object[] a, int i, int j )
    {
        Object x = a[i];
        a[i] = a[j];
        a[j] = x;
    }

    private static void shuffle( Object[] a )
    {
        for( int i=0 ; i!=a.length ; i++ )
            swap(a,i,i+rand(a.length-i));
    }

    public static void main( String[] args )
    {
        double sortingEfficiency;
        long t1,t2;
        int SIZE;
        SIZE = Integer.parseInt(args[0]);

        int MAX = 2000000000;
        if( args.length >= 4 && args[2].equals("-max") )
            MAX = Integer.parseInt(args[3]);

        double correction;
        {
            long total = 0;
            for( int k=0 ; k!=1e8 ; k++ )
            {
                t1 = System.nanoTime();
                t2 = System.nanoTime();
                total += t2-t1;
            }
            correction = total/1e8;
        }
        java.util.Locale.setDefault(new java.util.Locale("US"));
        log("Correction: "+correction+"%n");
        log("Threads:    "+THREADS+"%n");
        java.util.Date now = new java.util.Date();
        emit("%tF %tT;",now,now);
        emit("%s;",System.getProperty("os.name"));
        emit("%s;",System.getProperty("os.version"));
        emit("%s;",System.getProperty("java.vendor"));
        emit("%s;",System.getProperty("java.vm.version"));
        for( int i=2 ; i<args.length ; i++ ) emit("%s;",args[i]);

        if( args[1].equals("ssd") )
        {
            log("serialSort for double[%d]%n",SIZE);
            emit("ssd;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            double[] a = new double[SIZE];
            for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
            serialSort(a,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
                t1 = System.nanoTime();
                serialSort(a,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(a,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        if( args[1].equals("ssl") )
        {
            log("serialSort for long[%d]%n",SIZE);
            emit("ssl;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            long[] la = new long[SIZE];
            for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
            serialSort(la,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
                t1 = System.nanoTime();
                serialSort(la,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(la,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("ssi") )
        {
            log("serialSort for int[%d]%n",SIZE);
            emit("ssi;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            int[] ia = new int[SIZE];
            for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
            serialSort(ia,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
                t1 = System.nanoTime();
                serialSort(ia,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("ssf") )
        {
            log("serialSort for float[%d]%n",SIZE);
            emit("ssf;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            float[] fa = new float[SIZE];
            for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
            serialSort(fa,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
                t1 = System.nanoTime();
                serialSort(fa,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("ssI") )
        {
            log("serialSort for Integer[%d]%n",SIZE);
            emit("ssI;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            Integer[] A = new Integer[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = rand(MAX);
            serialSort(A,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                serialSort(A,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(A,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("ssS") )
        {
            log("serialSort for String[%d]%n",SIZE);
            emit("ssS;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            String[] A = new String[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = ""+rand(MAX);
            serialSort(A,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                serialSort(A,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(A,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.3f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("pssd") )
        {
            log("parallelSort for double[%d]%n",SIZE);
            emit("pssd;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            double[] a = new double[SIZE];
            for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
            parallelSort(a,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
                t1 = System.nanoTime();
                parallelSort(a,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(a,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("pssl") )
        {
            log("parallelSort for long[%d]%n",SIZE);
            emit("pssl;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            long[] la = new long[SIZE];
            for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
            parallelSort(la,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
                t1 = System.nanoTime();
                parallelSort(la,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(la,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("pssi") )
        {
            log("parallelSort for int[%d]%n",SIZE);
            emit("pssi;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            int[] ia = new int[SIZE];
            for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
            parallelSort(ia,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
                t1 = System.nanoTime();
                parallelSort(ia,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("pssf") )
        {
            log("parallelSort for float[%d]%n",SIZE);
            emit("pssf;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            float[] fa = new float[SIZE];
            for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
            parallelSort(fa,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
                t1 = System.nanoTime();
                parallelSort(fa,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("pssS") )
        {
            log("parallelSort for String[%d]%n",SIZE);
            emit("pssS;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            Comparable[] A = new String[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = ""+rand(MAX);
            parallelSort(A,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                parallelSort(A,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(A,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("pssI") )
        {
            log("parallelSort for Integer[%d]%n",SIZE);
            emit("pssI;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            Comparable[] A = new Integer[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = rand(MAX);
            parallelSort(A,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                parallelSort(A,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(A,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("psd") )
        {
            log("java.util.Arrays.parallelSort for double[%d]%n",SIZE);
            emit("psd;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            double[] a = new double[SIZE];
            for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
            java.util.Arrays.parallelSort(a,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.parallelSort(a,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(a,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("psl") )
        {
            log("java.util.Arrays.parallelSort for long[%d]%n",SIZE);
            emit("psl;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            long[] la = new long[SIZE];
            for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
            java.util.Arrays.parallelSort(la,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.parallelSort(la,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(la,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("psi") )
        {
            log("java.util.Arrays.parallelSort for int[%d]%n",SIZE);
            emit("psi;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            int[] ia = new int[SIZE];
            for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
            java.util.Arrays.parallelSort(ia,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.parallelSort(ia,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("si") )
        {
            log("java.util.Arrays.sort for int[%d]%n",SIZE);
            emit("si;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            int[] ia = new int[SIZE];
            for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
            java.util.Arrays.sort(ia,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.sort(ia,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("psf") )
        {
            log("java.util.Arrays.parallelSort for float[%d]%n",SIZE);
            emit("psf;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            float[] fa = new float[SIZE];
            for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
            java.util.Arrays.parallelSort(fa,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.parallelSort(fa,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("psS") )
        {
            log("java.util.Arrays.parallelSort for String[%d]%n",SIZE);
            emit("psS;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            Comparable[] A = new String[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = ""+rand(MAX);
            java.util.Arrays.parallelSort(A,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                java.util.Arrays.parallelSort(A,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(A,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("psI") )
        {
            log("java.util.Arrays.parallelSort for Integer[%d]%n",SIZE);
            emit("psI;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            Comparable[] A = new Integer[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = rand(MAX);
            java.util.Arrays.parallelSort(A,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                java.util.Arrays.parallelSort(A,0,SIZE);
                t2 = System.nanoTime();
                totalAll += t2-t1;
                count++;
            }
            verify(A,0,SIZE);
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("sd") )
        {
            log("java.util.Arrays.sort for double[%d]%n",SIZE);
            emit("sd;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            double[] a = new double[SIZE];
            for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
            java.util.Arrays.sort(a,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=a.length ; i++ ) a[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.sort(a);
                t2 = System.nanoTime();
                verify(a);
                count++;
                totalAll += t2-t1;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("sl") )
        {
            log("java.util.Arrays.sort for long[%d]%n",SIZE);
            emit("sl;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            long[] la = new long[SIZE];
            for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
            java.util.Arrays.sort(la,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=la.length ; i++ ) la[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.sort(la);
                t2 = System.nanoTime();
                verify(la);
                count++;
                totalAll += t2-t1;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("si") )
        {
            log("java.util.Arrays.sort for int[%d]%n",SIZE);
            emit("si;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            int[] ia = new int[SIZE];
            for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
            java.util.Arrays.sort(ia,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=ia.length ; i++ ) ia[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.sort(ia);
                t2 = System.nanoTime();
                count++;
                totalAll += t2-t1;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("sf") )
        {
            log("java.util.Arrays.sort for float[%d]%n",SIZE);
            emit("sf;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            float[] fa = new float[SIZE];
            for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
            java.util.Arrays.sort(fa,0,SIZE);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                for( int i=0 ; i!=fa.length ; i++ ) fa[i] = rand(MAX);
                t1 = System.nanoTime();
                java.util.Arrays.sort(fa);
                t2 = System.nanoTime();
                count++;
                totalAll += t2-t1;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("sI") )
        {
            log("java.util.Arrays.sort for Integer[%d]%n",SIZE);
            emit("sI;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            Comparable[] A = new Integer[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = rand(MAX);
            java.util.Arrays.sort(A);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                java.util.Arrays.sort(A);
                t2 = System.nanoTime();
                verify(A);
                count++;
                totalAll += t2-t1;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
        else if( args[1].equals("sS") )
        {
            log("java.util.Arrays.sort for String[%d]%n",SIZE);
            emit("sS;%d;",SIZE);
            int count = 0;
            long totalAll = 0;
            Comparable[] A = new String[SIZE];
            for( int i=0 ; i!=A.length ; i++ ) A[i] = ""+rand(MAX);
            java.util.Arrays.sort(A);
            System.gc();
            while( totalAll < (long)2e9 || count < 5 )
            {
                shuffle(A);
                t1 = System.nanoTime();
                java.util.Arrays.sort(A);
                t2 = System.nanoTime();
                verify(A);
                count++;
                totalAll += t2-t1;
            }
            sortingEfficiency = 1000.0*entropy(SIZE)*count/(totalAll-count*correction);
            log("Sorting time:         %.4f seconds%n",(totalAll-count*correction)/1.0e9/count);
            log("Sorting efficiency:   %.1f MHz%n",sortingEfficiency);
            emit("%.1f;",sortingEfficiency);
            emit("%.4f%n",(totalAll-count*correction)/1.0e9/count);
        }
    }

    static void emit( String fmt, Object... args )
    {
        System.out.printf(fmt,args);
    }

    static void log( String fmt, Object... args )
    {
        //System.out.printf(fmt,args);
    }
}
