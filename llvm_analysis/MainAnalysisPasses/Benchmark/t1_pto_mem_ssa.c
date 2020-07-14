#include<stdio.h>
#include<stdlib.h>

typedef struct data {
    int a,b;
} data;

typedef struct G {
    int a,b;
    data *p;
} G;

G g0,g1,g2,g3;
G g4,g5,g6,g7;

data d0,d1,d2,d3;

int ioctl0(int cmd, void *p);
int ioctl1(int cmd, void *p);

int foo0(data *p) {
    int r;
    if (!p) {
        return 0;
    }
    r = p->a + p->b;
    if (r > 8) {
        printf("r: %d\n",r);
    }else {
        printf("r is small\n");
    }
    return r;
}

int foo1(G *pg) {
    int r;
    if (!pg) {
        return 0;
    }
    data *p = pg->p;
    r = p->a + p->b;
    if (r > 8) {
        printf("r: %d\n",r);
    }else {
        printf("r is small\n");
    }
    return r;
}

int foo2(G *pg) {
    int r;
    if (!pg) {
        return 0;
    }
    data *p = pg->p;
    r = p->a + p->b;
    if (r > 8) {
        printf("r: %d\n",r);
    }else {
        printf("r is small\n");
    }
    return r;
}

int ioctl0(int cmd, void *p) {
    int res;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            //g6.p->a = ui->a;
            d0.a = ui->a;
            break;
        default:
            break;
    }
    return 0;
}

int ioctl2(int cmd, void *p) {
    int res;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            //g6.p->a = ui->a;
            d2.a = ui->a;
            break;
        default:
            break;
    }
    return 0;
}


int ioctl1(int cmd, void *p) {
    int res;
    G *pg;
    data *ui = (data*)p;
    switch(cmd) {
        case 0:
            pg = (ui->a ? &g6 : &g7);
            g6.p = &d2;
            if (ui->b) {
                g6.p = &d0;
                //Exp: g6.p can only point to d0.
                foo1(&g6);
            }else {
                g6.p = &d1;
                //Exp: g6.p can only point to d1.
                foo2(&g6);
            }
            //Exp: g6.p can point to both d0 and d1, but not d2!
            foo0(g6.p);
            pg->p = &d2;
            //Exp: g6.p can point to both d0 ,d1 and d2. (since 'pg' has multiple pto, although post-dom, this is a weak update for g6.p). 
            foo1(&g6);
            g6.p = &d3;
            //Exp: g6.p only points to d3 (post-dom and strong update).
            foo2(&g6);
            break;
        default:
            break;
    }
    return 0;
}

int main(int argc, char **argv){
    g6.p = &d0;
    ioctl0(argc,0);
    ioctl1(argc,0);
    ioctl2(argc,0);
    return 0;
}
