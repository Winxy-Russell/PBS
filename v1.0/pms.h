#ifndef _PMS_H_
#define _PMS_H_

#include <cmath>
#include "basis_pms.h"
#include "deci.h"
#include <sstream>
#include <algorithm>

Satlike::Satlike()
{
	problem_weighted = 1;
	partial = 1; //1 if the instance has hard clauses, and 0 otherwise.

	max_clause_length = 0;
	min_clause_length = 100000000;

	//size of the instance
	num_vars = 0;		 //var index from 1 to num_vars
	num_clauses = 0; //clause index from 0 to num_clauses-1
	num_hclauses = 0;
	num_sclauses = 0;

	print_time = 240;
	cutoff_time = 300;
}

void Satlike::settings()
{
	//steps
	max_tries = 100000000;
	max_flips = 200000000;
	max_non_improve_flip = 10000000;

	large_clause_count_threshold = 0;
	soft_large_clause_count_threshold = 0;

	rdprob = 0.01;
	hd_count_threshold = 15;
	rwprob = 0.1;
	smooth_probability = 0.01;

	h_inc = 1;
	softclause_weight_threshold = 1;

	if (num_vars > 2000)
	{
		rdprob = 0.01;
		hd_count_threshold = 15;
		rwprob = 0.1;
		smooth_probability = 0.0000001;
	}
}

void Satlike::allocate_memory()
{
	int malloc_var_length = num_vars + 10;
	int malloc_clause_length = num_clauses + 10;

	unit_clause = new lit[malloc_clause_length];

	var_lit = new lit *[malloc_var_length];
	var_lit_count = new int[malloc_var_length];
	clause_lit = new lit *[malloc_clause_length];
	clause_lit_count = new int[malloc_clause_length];
	clause_true_lit_thres = new int[malloc_clause_length];

	score = new long long[malloc_var_length];
	sscore = new long long[malloc_var_length];
	oscore = new long long[malloc_var_length];
	var_neighbor = new int *[malloc_var_length];
	var_neighbor_count = new int[malloc_var_length];
	time_stamp = new long long[malloc_var_length];
	neighbor_flag = new int[malloc_var_length];
	temp_neighbor = new int[malloc_var_length];

	org_clause_weight = new long long[malloc_clause_length];
	clause_weight = new long long[malloc_clause_length];
	unit_weight = new long long[malloc_clause_length];
	org_unit_weight = new long long[malloc_clause_length];
	sat_count = new int[malloc_clause_length];
	sat_var = new int[malloc_clause_length];
	clause_selected_count = new long long[malloc_clause_length];
	best_soft_clause = new int[malloc_clause_length];

	hardunsat_stack = new int[malloc_clause_length];
	index_in_hardunsat_stack = new int[malloc_clause_length];
	softunsat_stack = new int[malloc_clause_length];
	index_in_softunsat_stack = new int[malloc_clause_length];

	unsatvar_stack = new int[malloc_var_length];
	index_in_unsatvar_stack = new int[malloc_var_length];
	unsat_app_count = new int[malloc_var_length];

	goodvar_stack = new int[malloc_var_length];
	already_in_goodvar_stack = new int[malloc_var_length];

	cur_soln = new int[malloc_var_length];
	best_soln = new int[malloc_var_length];
	local_opt_soln = new int[malloc_var_length];

	large_weight_clauses = new int[malloc_clause_length];
	soft_large_weight_clauses = new int[malloc_clause_length];
	already_in_soft_large_weight_stack = new int[malloc_clause_length];

	best_array = new int[malloc_var_length];
	temp_lit = new int[malloc_var_length];
}

void Satlike::free_memory()
{
	int i;
	for (i = 0; i < num_clauses; i++)
		delete[] clause_lit[i];

	for (i = 1; i <= num_vars; ++i)
	{
		delete[] var_lit[i];
		delete[] var_neighbor[i];
	}

	delete[] var_lit;
	delete[] var_lit_count;
	delete[] clause_lit;
	delete[] clause_lit_count;
	delete[] clause_true_lit_thres;

	delete[] score;
	delete[] oscore;
	delete[] sscore;
	delete[] var_neighbor;
	delete[] var_neighbor_count;
	delete[] time_stamp;
	delete[] neighbor_flag;
	delete[] temp_neighbor;

	delete[] org_clause_weight;
	delete[] clause_weight;
	delete[] unit_weight;
	delete[] org_unit_weight;
	delete[] sat_count;
	delete[] sat_var;
	delete[] clause_selected_count;
	delete[] best_soft_clause;

	delete[] hardunsat_stack;
	delete[] index_in_hardunsat_stack;
	delete[] softunsat_stack;
	delete[] index_in_softunsat_stack;

	delete[] unsatvar_stack;
	delete[] index_in_unsatvar_stack;
	delete[] unsat_app_count;

	delete[] goodvar_stack;
	delete[] already_in_goodvar_stack;

	//delete [] fix;
	delete[] cur_soln;
	delete[] best_soln;
	delete[] local_opt_soln;

	delete[] large_weight_clauses;
	delete[] soft_large_weight_clauses;
	delete[] already_in_soft_large_weight_stack;

	delete[] best_array;
	delete[] temp_lit;
}

void Satlike::build_neighbor_relation()
{
	int i, j, count;
	int v, c, n;
	int temp_neighbor_count;

	for (v = 1; v <= num_vars; ++v)
	{
		neighbor_flag[v] = 1;
		temp_neighbor_count = 0;

		for (i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			for (j = 0; j < clause_lit_count[c]; ++j)
			{
				n = clause_lit[c][j].var_num;
				if (neighbor_flag[n] != 1)
				{
					neighbor_flag[n] = 1;
					temp_neighbor[temp_neighbor_count++] = n;
				}
			}
		}

		neighbor_flag[v] = 0;

		var_neighbor[v] = new int[temp_neighbor_count];
		var_neighbor_count[v] = temp_neighbor_count;

		count = 0;
		for (i = 0; i < temp_neighbor_count; i++)
		{
			var_neighbor[v][count++] = temp_neighbor[i];
			neighbor_flag[temp_neighbor[i]] = 0;
		}
	}
}

void Satlike::build_instance(char *filename)
{
	istringstream iss;
	char line[1024];
	string line2;
	char tempstr1[10];
	char tempstr2[10];
	int cur_lit;
	int i, v, c;
	//int     temp_lit[MAX_VARS];

	ifstream infile(filename);
	if (!infile)
	{
		cout << "c the input filename " << filename << " is invalid, please input the correct filename." << endl;
		exit(-1);
	}

	/*** build problem data structures of the instance ***/

	getline(infile, line2);

	while (line2[0] != 'p')
	{
		getline(infile, line2);
	}
	for (i = 0; i < 1024; i++)
	{
		line[i] = line2[i];
	}
	int read_items;
	read_items = sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);

	allocate_memory();

	for (c = 0; c < num_clauses; c++)
	{
		clause_lit_count[c] = 0;
		clause_true_lit_thres[c] = 1;
		clause_lit[c] = NULL;
	}

	for (v = 1; v <= num_vars; ++v)
	{
		var_lit_count[v] = 0;
		var_lit[v] = NULL;
		var_neighbor[v] = NULL;
	}

	num_hclauses = num_sclauses = 0;
	unit_clause_count = 0;
	//Now, read the clauses, one at a time.
	int lit_redundent, clause_redundent;
	int *temp_weight = new int[num_vars];
	int cur_weight;
	total_soft_weight = 0;

	c = 0;
	while (getline(infile, line2))
	{
		if (line2[0] == 'c')
			continue;
		else
		{
			iss.clear();
			iss.str(line2);
			iss.seekg(0, ios::beg);
		}
		clause_redundent = 0;
		clause_lit_count[c] = 0;

		iss >> org_clause_weight[c];
		iss >> clause_true_lit_thres[c];

		if (org_clause_weight[c] != top_clause_weight)
		{
			total_soft_weight += org_clause_weight[c];
			num_sclauses++;
		}
		else
			num_hclauses++;

		iss >> cur_weight;
		iss >> cur_lit;
		while (cur_weight != 0)
		{
			/*
			lit_redundent=0;
			for(int p=0; p<clause_lit_count[c]; p++)
			{
				if(cur_lit==temp_lit[p]){
					lit_redundent=1;
					break;
				}
				else if(cur_lit==-temp_lit[p]){
					clause_redundent=1;
					break;
				}
			}
			
			if(lit_redundent==0)
			{*/
			temp_weight[clause_lit_count[c]] = cur_weight;
			temp_lit[clause_lit_count[c]] = cur_lit;
			clause_lit_count[c]++;
			//}
			iss >> cur_weight;
			iss >> cur_lit;
		}

		//if(clause_redundent==0) //the clause is not tautology
		//{
		clause_lit[c] = new lit[clause_lit_count[c] + 1];

		for (i = 0; i < clause_lit_count[c]; ++i)
		{
			clause_lit[c][i].clause_num = c;
			clause_lit[c][i].var_num = abs(temp_lit[i]);
			clause_lit[c][i].weight = temp_weight[i];

			if (temp_lit[i] > 0)
				clause_lit[c][i].sense = 1;
			else
				clause_lit[c][i].sense = 0;

			var_lit_count[clause_lit[c][i].var_num]++;
		}
		clause_lit[c][i].var_num = 0;
		clause_lit[c][i].clause_num = -1;
		clause_lit[c][i].weight = 0;

		if (clause_lit_count[c] == 1)
		{
			unit_clause[unit_clause_count++] = clause_lit[c][0];
		}

		if (clause_lit_count[c] > max_clause_length)
			max_clause_length = clause_lit_count[c];
		if (clause_lit_count[c] < min_clause_length)
			min_clause_length = clause_lit_count[c];

		c++;
		//}
		//else
		//{
		//	num_clauses--;
		//	clause_lit_count[c] = 0;
		//}
	}
	infile.close();

	//creat var literal arrays
	for (v = 1; v <= num_vars; ++v)
	{
		var_lit[v] = new lit[var_lit_count[v] + 1];
		var_lit_count[v] = 0; //reset to 0, for build up the array
	}
	//scan all clauses to build up var literal arrays
	for (c = 0; c < num_clauses; ++c)
	{
		for (i = 0; i < clause_lit_count[c]; ++i)
		{
			v = clause_lit[c][i].var_num;
			var_lit[v][var_lit_count[v]] = clause_lit[c][i];
			++var_lit_count[v];
		}
	}
	for (v = 1; v <= num_vars; ++v)
		var_lit[v][var_lit_count[v]].clause_num = -1;

	build_neighbor_relation();

	best_soln_feasible = 0;
	opt_unsat_weight = total_soft_weight + 1;
}

void Satlike::init(vector<int> &init_solution)
{
	int v, c;
	int j;

	local_soln_feasible = 0;
	local_opt_unsat_weight = top_clause_weight + 1;
	large_weight_clauses_count = 0;
	soft_large_weight_clauses_count = 0;

	//consider:ave_soft_weight = total_soft_weight / num_sclauses;
	ave_hard_weight = 0;
	inc_hard_weight = 0;
	//cout << "ave soft weight is " << ave_soft_weight << endl;
	//Initialize clause information
	for (c = 0; c < num_clauses; c++)
	{
		clause_selected_count[c] = 0;

		//clause_weight[c] = clause_true_lit_thres[c];
		org_unit_weight[c] = 1;
		unit_weight[c] = org_unit_weight[c];
		long long total_sum = 0;
		for (int i = 0; i < clause_lit_count[c]; ++i)
		{
		    total_sum += clause_lit[c][i].weight;
		}
		clause_weight[c] = total_sum / clause_lit_count[c];
		ave_hard_weight += clause_weight[c];
	}
	inc_hard_weight = ave_hard_weight % num_hclauses;
	ave_hard_weight /= num_hclauses;
	// consider:inc_hard_weight += ave_soft_weight;
	//cout << "inc hard weight is " << inc_hard_weight << endl;
	//cout << "ave hard weight is " << ave_hard_weight << endl;

	//init solution
	if (init_solution.size() == 0)
	{
		for (v = 1; v <= num_vars; v++)
		{
			cur_soln[v] = 0;
			time_stamp[v] = 0;
			unsat_app_count[v] = 0;
		}
	}
	else
	{
		for (v = 1; v <= num_vars; v++)
		{
			cur_soln[v] = init_solution[v];
			if (cur_soln[v] == 2)
				cur_soln[v] = rand() % 2;
			time_stamp[v] = 0;
			unsat_app_count[v] = 0;
		}
	}

	//init stacks
	hard_unsat_nb = 0;
	hardunsat_stack_fill_pointer = 0;
	//softunsat_stack_fill_pointer = 0;
	unsatvar_stack_fill_pointer = 0;
	/* figure out sat_count, sat_var, soft_unsat_weight and init unsat_stack */
	//soft_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		sat_count[c] = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{

			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				sat_count[c] += clause_lit[c][j].weight;
				sat_var[c] = clause_lit[c][j].var_num;
			}
		}
		if (sat_count[c] < clause_true_lit_thres[c])
		{
			if (org_clause_weight[c] != top_clause_weight)
				soft_unsat_weight += (clause_true_lit_thres[c] - sat_count[c]) * org_unit_weight[c];
			unsat(c);
		}
	}

	/*figure out score*/
	int sense, weight;
	for (v = 1; v <= num_vars; v++)
	{
		score[v] = 0;

		for (int i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			sense = var_lit[v][i].sense;
			weight = var_lit[v][i].weight;
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						score[v] += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						score[v] -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						score[v] -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}

		}
	}

	//init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v = 1; v <= num_vars; v++)
	{
		if (score[v] > 0)
		{
			already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
			mypush(v, goodvar_stack);
		}
		else
			already_in_goodvar_stack[v] = -1;
	}
}

int Satlike::pick_var()
{
	int i, v;
	int best_var;

	if (goodvar_stack_fill_pointer > 0)
	{
		if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
			return goodvar_stack[rand() % goodvar_stack_fill_pointer];
        // Few variables to be picked
		if (goodvar_stack_fill_pointer < hd_count_threshold)
		{
			best_var = goodvar_stack[0];
			for (i = 1; i < goodvar_stack_fill_pointer; ++i)
			{
				v = goodvar_stack[i];
				if (score[v] > score[best_var])
					best_var = v;
				else if (score[v] == score[best_var])
				{
					if (time_stamp[v] < time_stamp[best_var])
						best_var = v;
				}
			}
			return best_var;
		}
		else
		{

			int r = rand() % goodvar_stack_fill_pointer;
			best_var = goodvar_stack[r];

			for (i = 1; i < hd_count_threshold; ++i)
			{
				r = rand() % goodvar_stack_fill_pointer;
				v = goodvar_stack[r];
				if (score[v] > score[best_var])
					best_var = v;
				else if (score[v] == score[best_var])
				{
					if (time_stamp[v] < time_stamp[best_var])
						best_var = v;
				}
			}
			return best_var;
		}
	}
	update_clause_weights();
	int sel_c;
	lit *p;

	if (hardunsat_stack_fill_pointer > 0)
	{
		sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
	}
	else
	{
        printf("1. All of the constraints are satisfiable");
        return -1;
	}
	if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
		return clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
	best_var = clause_lit[sel_c][0].var_num;
	p = clause_lit[sel_c];
	for (p++; (v = p->var_num) != 0; p++)
	{
		if (score[v] > score[best_var])
			best_var = v;
		else if (score[v] == score[best_var])
		{
			if (time_stamp[v] < time_stamp[best_var])
				best_var = v;
		}
	}
	return best_var;
}

void Satlike::update_goodvarstack1(int flipvar)
{
	int v;

	//remove the vars no longer goodvar in goodvar stack
	for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
	{
		v = goodvar_stack[index];
		//把最后一个元素填入当前位置
		if (score[v] <= 0)
		{
			int top_v = mypop(goodvar_stack);
			goodvar_stack[index] = top_v;
			already_in_goodvar_stack[top_v] = index;
			already_in_goodvar_stack[v] = -1;
		}
	}

	//add goodvar
	for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
	{
		v = var_neighbor[flipvar][i];
		if (score[v] > 0)
		{
			if (already_in_goodvar_stack[v] == -1)
			{
				already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
				mypush(v, goodvar_stack);
			}
		}
	}
}
void Satlike::update_goodvarstack2(int flipvar)
{
	if (score[flipvar] > 0 && already_in_goodvar_stack[flipvar] == -1)
	{
		already_in_goodvar_stack[flipvar] = goodvar_stack_fill_pointer;
		mypush(flipvar, goodvar_stack);
	}
	else if (score[flipvar] <= 0 && already_in_goodvar_stack[flipvar] != -1)
	{
		int index = already_in_goodvar_stack[flipvar];
		int last_v = mypop(goodvar_stack);
		goodvar_stack[index] = last_v;
		already_in_goodvar_stack[last_v] = index;
		already_in_goodvar_stack[flipvar] = -1;
	}
	int i, v;
	for (i = 0; i < var_neighbor_count[flipvar]; ++i)
	{
		v = var_neighbor[flipvar][i];
		if (score[v] > 0)
		{
			if (already_in_goodvar_stack[v] == -1)
			{
				already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
				mypush(v, goodvar_stack);
			}
		}
		else if (already_in_goodvar_stack[v] != -1)
		{
			int index = already_in_goodvar_stack[v];
			int last_v = mypop(goodvar_stack);
			goodvar_stack[index] = last_v;
			already_in_goodvar_stack[last_v] = index;
			already_in_goodvar_stack[v] = -1;
		}
	}
}

void Satlike::flip(int flipvar)
{
	int i, v, c;
	int index;
	lit *clause_c;
	int weight;
	int gap;

	int org_flipvar_score = score[flipvar];

	cur_soln[flipvar] = 1 - cur_soln[flipvar];

	for (i = 0; i < var_lit_count[flipvar]; ++i)
	{
		c = var_lit[flipvar][i].clause_num;
		clause_c = clause_lit[c];
		weight = var_lit[flipvar][i].weight;
		if (org_clause_weight[c] == top_clause_weight)
		{
			if (cur_soln[flipvar] == var_lit[flipvar][i].sense)
			{

				//sat_count[c] += weight;

				if (sat_count[c] + weight <= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							score[v] -= (unit_weight[c] * (min(gap, p->weight) - min(gap - weight, p->weight)));
						}
					}
				}
				else if (sat_count[c] <= clause_true_lit_thres[c]) //sat_count[c]+weight > clause_true_lit_thres[c]
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							score[v] -= (unit_weight[c] * min(gap, p->weight));
						}
						else
						{
							score[v] += unit_weight[c] * (p->weight - max(0, gap - weight + p->weight));
						}
					}
				}
				else //sat_count[c]+weight > clause_true_lit_thres[c], sat_count[c] > clause_true_lit_thres[c]
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] += unit_weight[c] * (max(0, gap + p->weight) - max(0, gap - weight + p->weight));
						}
					}
				}
				if (sat_count[c] < clause_true_lit_thres[c] && sat_count[c] + weight >= clause_true_lit_thres[c])
				{
					sat(c);
				}
				sat_count[c] += weight;
			}
			else // cur_soln[flipvar] != cur_lit.sense
			{
				//--sat_count[c];
				if (sat_count[c] - weight >= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] -= unit_weight[c] * (max(0, gap + weight + p->weight) - max(0, gap + p->weight));
						}
					}
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] -= unit_weight[c] * (p->weight - max(0, gap + p->weight));
						}
						else
						{
							score[v] += unit_weight[c] * min(p->weight, gap + weight);
						}
					}
				}
				else
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							score[v] += unit_weight[c] * (min(p->weight, gap + weight) - min(p->weight, gap));
						}
					}
				}
				if (sat_count[c] >= clause_true_lit_thres[c] && sat_count[c] - weight < clause_true_lit_thres[c])
				{
					unsat(c);
				}
				sat_count[c] -= weight;

			} //end else
		}

	}

	//update information of flipvar
	score[flipvar] = -org_flipvar_score;
	update_goodvarstack1(flipvar);
}

void Satlike::local_search(vector<int> &init_solution)
{
	settings();
	max_flips = 200000000;
	init(init_solution);
	cout << "time is " << get_runtime() << endl;
	cout << "hard unsat nb is " << hard_unsat_nb << endl;
	cout << "soft unsat nb is " << soft_unsat_weight << endl;
	cout << "goodvar nb is " << goodvar_stack_fill_pointer << endl;
}

void Satlike::print_best_solution()
{
	if (best_soln_feasible == 1)
	{

		if (verify_sol())
			cout << opt_unsat_weight << '\t' << opt_time << '\t' << tries << '\t' << step << endl;
		else
			cout << "verify solion wrong " << endl;
	}
	else
		cout << "no feasible solution" << endl;

	ofstream ofile("solution.res");
	ofile << num_vars << " ";
	for (int i = 1; i <= num_vars; i++)
	{
		ofile << best_soln[i] << " ";
	}
	ofile << endl;
}

void Satlike::local_search_with_decimation(vector<int> &init_solution, char *inputfile)
{
	settings();
	for (tries = 1; tries < max_tries; ++tries)
	{
		init(init_solution);
		for (step = 1; step < max_flips; ++step)
		{
			if (hard_unsat_nb == 0 &&  best_soln_feasible == 0)
			{
				//cout << "unsat soft stack fill pointer" << softunsat_stack_fill_pointer << endl;
				if (soft_unsat_weight < top_clause_weight)
				{
					softclause_weight_threshold += 0;
					best_soln_feasible = 1;
					opt_unsat_weight = soft_unsat_weight;
					opt_time = get_runtime();
					for (int v = 1; v <= num_vars; ++v)
						best_soln[v] = cur_soln[v];

					if (opt_unsat_weight == 0)
					{
						return;
					}
				}
			}
			if (step % 1000 == 0)
			{
				double elapse_time = get_runtime();
				if (elapse_time >= cutoff_time)
				{
					return;
				}
			}
			int flipvar = pick_var();

			flip(flipvar);
			//check_new_score();
			time_stamp[flipvar] = step;
		}
	}
}

void Satlike::check_softunsat_weight()
{
	int c, j, flag;
	long long verify_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		flag = 0;
		int tem_clause_true_lit_count = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				tem_clause_true_lit_count++;
			}
		}
		if (tem_clause_true_lit_count >= clause_true_lit_thres[c])
			flag = 1;

		if (flag == 0)
		{
			if (org_clause_weight[c] == top_clause_weight) //verify hard clauses
			{
				continue;
			}
			else
			{
				verify_unsat_weight += org_unit_weight[c] * (clause_true_lit_thres[c] - tem_clause_true_lit_count);
			}
		}
	}

	if (verify_unsat_weight != soft_unsat_weight)
	{
		cout << step << endl;
		cout << "verify unsat weight is" << verify_unsat_weight << " and soft unsat weight is " << soft_unsat_weight << endl;
	}
	//return 0;
}

bool Satlike::verify_sol()
{
	int c, j, flag;
	long long verify_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		flag = 0;
		int tem_clause_true_lit_count = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (best_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				tem_clause_true_lit_count += clause_lit[c][j].weight;
			}
		}
		if (tem_clause_true_lit_count >= clause_true_lit_thres[c])
			flag = 1;

		if (flag == 0)
		{
			if (org_clause_weight[c] == top_clause_weight) //verify hard clauses
			{
				//output the clause unsatisfied by the solution
				cout << "c Error: hard clause " << c << " is not satisfied" << endl;

				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
				{
					if (clause_lit[c][j].sense == 0)
						cout << "-";
					cout << clause_lit[c][j].var_num << " ";
				}
				cout << endl;
				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
					cout << best_soln[clause_lit[c][j].var_num] << " ";
				cout << endl;
				return 0;
			}
			else
			{
				verify_unsat_weight += org_unit_weight[c] * (clause_true_lit_thres[c] - tem_clause_true_lit_count);
				/*
				cout << "c wanning: soft clause " << c << " is not satisfied" << endl;

				cout << "c org clause weight " << org_clause_weight[c] << " " << endl;

				for (j = 0; j < clause_lit_count[c]; ++j)
				{
					if (clause_lit[c][j].sense == 0)
						cout << "-";
					cout << clause_lit[c][j].var_num << " ";
				}
				cout << endl;
				//cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
					cout << best_soln[clause_lit[c][j].var_num] << " ";
				cout << endl;*/
				//return 0;
			}
		}
	}

	if (verify_unsat_weight == opt_unsat_weight)
		return 1;
	else
	{
		cout << "c Error: find opt=" << opt_unsat_weight << ", but verified opt=" << verify_unsat_weight << endl;
	}
	return 0;
}

void Satlike::simple_print()
{
	if (best_soln_feasible == 1)
	{
		if (verify_sol() == 1)
			cout << opt_unsat_weight << '\t' << opt_time << endl;
		else
			cout << "solution is wrong " << endl;
	}
	else
		cout << -1 << '\t' << -1 << endl;
}

void Satlike::increase_weights()
{
	int i, c, v;
	int weight;

	int flag = 0;
	//long long inc_hard_weight;
	for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
	{
		c = hardunsat_stack[i];

		inc_hard_weight += clause_weight[c];
		//clause_weight[c] += (h_inc * clause_true_lit_thres[c]);
		//cout << "c: " << c << endl;
		unit_weight[c] += h_inc;

		for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
		{
			weight = p->weight;
			if (p->sense != cur_soln[v])
			{
				score[v] += h_inc * min(clause_true_lit_thres[c] - sat_count[c], weight);
				if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
				{
					already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
					mypush(v, goodvar_stack);
				}
			}
			else
			{
				score[v] -= h_inc * weight;
				if (already_in_goodvar_stack[v] != -1 && score[v] + sscore[v] <= 0)
				{
					int top_v = mypop(goodvar_stack);
					goodvar_stack[already_in_goodvar_stack[v]] = top_v;
					already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
					already_in_goodvar_stack[v] = -1;
				}
			}
		}
	}

	//cout << "now ave hard weight is " << ave_hard_weight << endl; && ave_soft_weight - ave_hard_weight > 400
	if (soft_unsat_weight >= opt_unsat_weight && ave_soft_weight - ave_hard_weight < 100)
	{
		//flag = 1;
		ave_soft_weight += total_soft_weight / num_sclauses;
		inc_hard_weight += total_soft_weight / num_sclauses;
		for (c = 0; c < num_clauses; ++c)
		{
			if (org_clause_weight[c] == top_clause_weight)
				continue;

			unit_weight[c] += org_unit_weight[c];

			if (sat_count[c] < clause_true_lit_thres[c])
			{
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					sscore[v] += org_unit_weight[c];
					//min(clause_true_lit_thres[c] - sat_count[c], weight);
					if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
					{
						already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
						mypush(v, goodvar_stack);
					}
				}
			}
			else if (sat_count[c] == 1)
			{
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					//weight = p->weight;
					//sscore[v] += org_unit_weight[c];
					if (p->sense == cur_soln[v])
					{
						sscore[v] -= org_unit_weight[c];
						if (already_in_goodvar_stack[v] != -1 && score[v] + sscore[v] <= 0)
						{
							int top_v = mypop(goodvar_stack);
							goodvar_stack[already_in_goodvar_stack[v]] = top_v;
							already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
							already_in_goodvar_stack[v] = -1;
						}
					}
				}
			}
		}
	}

	ave_hard_weight += (inc_hard_weight / num_hclauses);
	inc_hard_weight %= num_hclauses;
}

void Satlike::smooth_weights()
{
	int i, clause, v;
	int weight;
	if (soft_unsat_weight < opt_unsat_weight && ave_soft_weight > (total_soft_weight / num_sclauses))
	{
		ave_soft_weight -= (total_soft_weight / num_sclauses);
		inc_hard_weight -= (total_soft_weight / num_sclauses);
		if (inc_hard_weight < 0)
			inc_hard_weight = 0;
		for (int c = 0; c < num_clauses; ++c)
		{
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (unit_weight[c] == 1 && sat_count[c] < clause_true_lit_thres[c])
					continue;

				unit_weight[c]--;
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					weight = p->weight;
					if (p->sense == cur_soln[v])
					{
						if (sat_count[c] - weight < clause_true_lit_thres[c])
						{
							score[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
							if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
						}
					}
				}
			}
			else
			{
				unit_weight[c]--;
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					weight = p->weight;
					if (p->sense == cur_soln[v])
					{
						if (sat_count[c] - weight < clause_true_lit_thres[c])
						{
							sscore[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
							if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
						}
					}
				}
			}
		}
	}
	else
	{
		for (int c = 0; c < num_clauses; ++c)
		{
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (unit_weight[c] == 1 && sat_count[c] < clause_true_lit_thres[c])
					continue;

				unit_weight[c]--;
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					weight = p->weight;
					if (p->sense == cur_soln[v])
					{
						if (sat_count[c] - weight < clause_true_lit_thres[c])
						{
							score[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
							if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
						}
					}
				}
			}
		}
	}
}

void Satlike::update_clause_weights()
{
	/*
	if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability)
	{
		smooth_weights();
	}
	else
	{*/
	increase_weights();
	//}
}

inline void Satlike::unsat(int clause)
{
	if (org_clause_weight[clause] == top_clause_weight)
	{
		index_in_hardunsat_stack[clause] = hardunsat_stack_fill_pointer;
		mypush(clause, hardunsat_stack);
		hard_unsat_nb++;
	}
	else
	{
		index_in_softunsat_stack[clause] = softunsat_stack_fill_pointer;
		mypush(clause, softunsat_stack);
		//soft_unsat_weight += org_clause_weight[clause];
	}
}

inline void Satlike::sat(int clause)
{
	int index, last_unsat_clause;

	if (org_clause_weight[clause] == top_clause_weight)
	{

		last_unsat_clause = mypop(hardunsat_stack);
		index = index_in_hardunsat_stack[clause];
		hardunsat_stack[index] = last_unsat_clause;
		index_in_hardunsat_stack[last_unsat_clause] = index;

		hard_unsat_nb--;
	}
	else
	{
		last_unsat_clause = mypop(softunsat_stack);
		index = index_in_softunsat_stack[clause];
		softunsat_stack[index] = last_unsat_clause;
		index_in_softunsat_stack[last_unsat_clause] = index;

		//soft_unsat_weight -= org_clause_weight[clause];
	}
}

void Satlike::check_new_score()
{
	long long tem_score = 0;
	long long tem_sscore = 0;
	int sense, c, v, i;
	int weight;
	for (v = 1; v <= num_vars; v++)
	{
		tem_score = 0;
		tem_sscore = 0;
		for (i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			sense = var_lit[v][i].sense;
			weight = var_lit[v][i].weight;
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						tem_score += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						tem_score -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						tem_score -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
			else
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						tem_sscore += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						tem_sscore -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						tem_sscore -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
		}
		if (tem_score != score[v] || tem_sscore != sscore[v])
		{

			cout << "score is worng in variable " << v << endl;
			cout << "tem_score is " << tem_score << endl;
			cout << "score function is " << score[v] << endl;
			cout << "flip num is " << step << endl;

			for (i = 0; i < var_lit_count[v]; ++i)
			{
				c = var_lit[v][i].clause_num;
				sense = var_lit[v][i].sense;
				weight = var_lit[v][i].weight;
				cout << c << " ";
			}
			cout << endl;
			exit(0);
			break;
		}
	}

	int tem_unsat_softweight = 0;
	for (int i = 0; i < num_clauses; ++i)
	{
		if (org_clause_weight[i] == top_clause_weight)
			continue;
		if (sat_count[i] < clause_true_lit_thres[i])
		{
			tem_unsat_softweight += (clause_true_lit_thres[i] - sat_count[i]);
		}
	}
	if (tem_unsat_softweight != soft_unsat_weight)
	{
		cout << "verify softunsat weight wrong " << endl;
		exit(0);
	}
}

#endif
