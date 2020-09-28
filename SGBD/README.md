
[`GROUP BY` vs `DISTINCT`](https://stackoverflow.com/questions/581521/whats-faster-select-distinct-or-group-by-in-mysql)

List all tables on http://adminer.ensimag.fr.
```sql
SELECT * FROM all_tables WHERE TABLESPACE_NAME='USERS';
```

## TD Hotels.
```sql
-- Q3
SELECT DISTINCT NomS FROM RESORTS NATURAL JOIN HOTELS WHERE TypeS='mer' AND CatH='4'; 

-- Q4
SELECT DISTINCT NomCl, AdrCl FROM GUESTS NATURAL JOIN BOOKINGS NATURAL JOIN RESORTS WHERE TypeS='montagne';
SELECT DISTINCT NomCl, AdrCl FROM GUESTS, BOOKINGS, RESORTS WHERE Guests.NCL = Bookings.NCL AND Bookings.NS = Resorts.NS AND Resorts.TypeS='montagne';

-- Q5
SELECT NCH, Hotels.NH, Rooms.NS FROM ROOMS, HOTELS, RESORTS
WHERE Rooms.NS = Hotels.NS AND Hotels.NH = Rooms.NH AND Resorts.NS = Hotels.NS
AND Resorts.TypeS = 'montagne' AND Hotels.CatH = '2' AND Rooms.Prix < 50;

-- Q8
SELECT h.ns, h.nh, h.nomh from hotels h, rooms ro where cath=4 and ro.ns = h.ns and ro.nh = h.nh group by h.ns, h.nh, h.nomh having min(ro.typch) = 'SDB';

SELECT distinct h.ns, h.nh, h.nomh 
from hotels h, rooms ro 
where catH = 4 
and ro.ns = h.ns and ro.nh = h.nh 
and ro.typch = all
(select typch from rooms where typch = 'SDB');

-- Q9

```

## TP EMP

```sql
-- Q1
select empno, ename from emp

-- Q2
select empno, ename, hiredate from emp where deptno = 20

-- Q3
select sum(sal) from emp

-- Q4
select empno, ename, job, sal from emp where job = 'MANAGER' and sal > 2800

-- Q5
select empno, ename from emp join dept on emp.deptno = dept.deptno where loc = 'DALLAS'

-- Q6
select empno, ename, job, sal from emp where deptno = 30 order by sal ASC

-- Q7
select distinct job from emp

-- Q8
select empno, ename from emp where ename like 'M%' and sal >= 1290

-- Q9
select emp.deptno, loc from emp join dept on emp.deptno = dept.deptno where ename = 'ALLEN'

-- Q10
select distinct emp.deptno, dname from emp join dept on emp.deptno = dept.deptno where job in ('CLERK', 'SALESMAN', 'ANALYST')

-- Q11
select distinct t2.empno, t2.ename from emp t1 join emp t2 on t1.mgr = t2.empno where t1.comm is not NULL and t2.job = 'MANAGER'

-- Q12
select empno, ename from emp join dept on emp.deptno = dept.deptno where loc in ('DALLAS', 'CHICAGO') and sal > 1000

-- Q13
select dept.deptno, dname, job, sum(sal), count(empno), avg(sal) from dept join emp on emp.deptno = dept.deptno group by dept.deptno, dname, job having count(empno) > 2

-- Q14

```
