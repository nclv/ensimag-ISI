#ifndef _PARCOURS_TABLEAU_BIDIMENSIONNEL_
#define _PARCOURS_TABLEAU_BIDIMENSIONNEL_

extern void line_max(double **matrix, double *array);
extern void col_min(double **matrix, double *array);

extern void line_max_col_min(double **matrix, double *array_line, double *array_col);
extern void line_max_col_min_opti(double **matrix, double *array_line, double *array_col);
extern void line_max_col_min_block(double **matrix, double *array_line, double *array_col);

#endif