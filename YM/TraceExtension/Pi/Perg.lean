import YM.TraceExtension.Pi.Valor
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}
open Complex
variable (d i b:Axis)(a:G.ColorIndex)
def effectP(p:Land)(s x k l:Axis):ℝ:=cof (p 0) i s x * cof (p 1) i k l + cof (p 1) i s x * cof (p 0) i k l
def derm(s x k l:Axis)(p:Track):ℝ:= cof p i s x*cof p i k l
lemma lead_s (y s x k l:Axis)(p:Land) : lotR i a p (pairDeriv G s x y k l+pairDeriv G k l y s x)= -Complex.I*↑(effectP i p s x k l) * (↑(p 0 y+p 1 y):ℂ):=by rw[map_add, crest_der,crest_der]; unfold effectP; push_cast;ring
lemma lawn_sum (y:Dish)(z:Axis): lawn d b y 0 z + lawn d b y 1 z= if z=b then (y.2:ℝ) else 0:=by simp [lawn,flee,mornA,mul_ite]
lemma lag_dr (y s x k l:Axis): lag d i b a (pairDeriv G s x y k l+pairDeriv G k l y s x)= if b=y then -2*(↑(derm i s x k l (step d)):ℂ) else 0:=by
   unfold lag; change Complex.I*PanZ (fun e=> FlopZ fun v=> lotR i a (lawn d b (e,v)) _) =_; simp_rw [lead_s, lawn_sum]
   by_cases ht:b=y
   · subst y; simp only [if_true]
     have hp(p q:Track)(s x): cof (p+q) i s x=cof p i s x+cof q i s x:=by unfold cof; simp only [Pi.add_apply];ring
     have ht(p:Track)(c:ℝ)(s x): cof (c • p) i s x=c*cof p i s x:=by unfold cof;simp only [Pi.smul_apply,smul_eq_mul];ring
     have hh(p:Track)(s x): cof (-p) i s x= -cof p i s x :=by simpa using ht p (-1) s x
     let V:ℂ:= ↑(derm i s x k l (step d))
     have he(e:ℤ): FlopZ (fun v:ℤ=> -Complex.I*↑(effectP i (lawn d b (e,v)) s x k l)*↑(v:ℝ))=(e:ℂ)^(2:ℕ)*(2*Complex.I*V):=by
          unfold effectP lawn flee; rw[flopi]; simp only [Matrix.cons_val_zero,Matrix.cons_val_one,ht,hp,hh];
          unfold V derm; push_cast;ring
     rw [funext he,pan_coeff _ _ (by decide),if_pos rfl]; unfold V; linear_combination (2*(↑(derm i s x k l (step d)):ℂ))*Complex.I_mul_I
   simp[ht,Ne.symm ht, flopi,pani]
lemma parch (w:Fin 3→ℝ)(b:Axis):
    let X(s):=derm i b s b s (step d); let U:=bareVector (G:=G) w
    lag d i b a (U.val b)= ((-2:ℂ)* (w 0:ℂ) * ∑ s:Axis,(↑(X s):ℂ)) + (-2:ℂ)*(w 1:ℂ)*(∑ t:Axis,∑ s:Axis,(↑(derm i t s t s (step d)):ℂ)):=by
    intro X U; let H:= (lag d i b a).restrictScalars ℝ; change H _=_; rw[euler (G:=G)]; rw[map_add,map_add,map_smul,map_smul,map_smul,map_sum,map_sum,map_sum];
    let V(s x k l y: Axis):= (if b=y then -(2:ℂ)*↑(derm i s x k l (step d)) else 0); have hw(s x k l y: Axis): H (pairDeriv G s x y k l+pairDeriv G k l y s x)=V s x k l y:= lag_dr ..
    simp_rw [map_sum]
    -- last shear ordering: pair b i a a i + pair a i a b i
    simp_rw[hw]; simp only [V,if_true]; rw [sum_congr rfl (g:=fun _=> (0:ℂ)) (fun k (_:k∈ univ.erase b)=>by simp [Ne.symm (ne_of_mem_erase (by assumption : k∈ _))])]
    simp only[sum_const_zero,smul_zero,add_zero,Complex.real_smul, X,← mul_sum]; ring
lemma lag_paid (w: Fin 3→ℝ): (∑ b, lag 0 1 b a ((bareVector w).val b))= (-4:ℂ)* ((w 0:ℂ)+4*(w 1:ℂ)):=by
   simp_rw [parch]; norm_num +decide only [derm, cof, Fin.sum_univ_four, step_apply,basis_eq]; norm_num; ring
lemma arch_rho (v: RawOne G)(h:G.Simple): archK a v.val= (12:ℂ)*↑(rho h v):=by
   obtain ⟨w,rfl⟩:= (bareCoordinates h).surjective v; rw[prism a _ h,lag_paid a,rho_vector]; push_cast; rfl
end YM.Trace.Kits
