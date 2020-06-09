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
            g0.a = ui->a;
            break;
        case 1:
            g1.b = g0.a;
            break;
        case 2:
            g2.a = g1.b;
            break;
        case 3:
            g3.b = g2.a;
            break;
        case 4:
            g5.b = g4.a;
            break;
        case 5:
            g7.b = g6.a;
            break;
        case 6:
            g6.p->a = ui->a;
            break;
        default:
            res = g3.b * 0xffff;
            printf("res: %d\n",res);
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
            g4.a = ui->b;
            break;
        case 1:
            pg = (ui->a ? &g6 : &g7);
            if (ui->b) {
                g6.p = &d0;
                //Exp: g6.p can only point to d0.
                foo1(&g6);
            }else {
                g6.p = &d1;
                //Exp: g6.p can only point to d1.
                foo2(&g6);
            }
            //Exp: g6.p can point to both d0 and d1.
            foo0(g6.p);
            pg->p = &d2;
            //Exp: both g6.p can point to both d0 ,d1 and d2. (since 'pg' has multiple pto, although post-dom, this is a weak update for g6.p). 
            foo1(&g6);
            g6.p = &d2;
            //Exp: g6.p only points to d2 (post-dom and strong update).
            foo2(&g6);
            g6.a = g5.b;
            break;
        default:
            res = g7.b * 0xffff;
            printf("res: %d\n",res);
            break;
    }
    return 0;
}

int main(int argc, char **argv){
    g6.p = &d0;
    ioctl0(argc,0);
    ioctl1(argc,0);
    return 0;
}
