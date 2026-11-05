import YM.TraceExtension.Xo.Ware
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Xo
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{F H:Maze G n}{Y Y':Gal G n}{a A:ℝ}
lemma lush_minus (h:Cloaked Y)(hp:Cloaked Y'): lush (Y-Y') ∘ input G n =ᶠ[𝓝 0] lush Y ∘ input G n - lush Y' ∘ input G n:=by
    have ht {Y:Gal G n}(h:Cloaked Y): ∀ᶠ x:Link G n in 𝓝 0, ContDiffAt ℝ ω (Y ∘ maroon G n (input G n x)) 0:=by
       let F(v:Link G n×Link G n):=input G n v.2*input G n v.1; have he:ContDiffAt ℝ ω (Y ∘ F) 0:=h.put F ((Army.powL (v:=Prod.snd) contDiffAt_snd).mul (Army.powL contDiffAt_fst)) (by simp[F]); let Z(x:Link G n):=(x,(0:Link G n))
       filter_upwards [(show Tendsto Z (𝓝 0) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (he.eventually (by simp))] with x hx
       exact (hx.comp (f:=fun y:Link G n=> (x,y)) 0 (by fun_prop))
    filter_upwards [ht h,ht hp] with x hx hv; let U:=input G n x
    change lush _ U=lush Y U - lush Y' U; rw[tether (Y-Y') U (hx.sub hv),tether _ _ hx,tether _ _ hv, ← sum_sub_distrib]; apply sum_congr rfl fun i _=>?_
    unfold outD; let P{Y:Gal G n}:=Y ∘ maroon G n U; have hu : DifferentiableAt ℝ (fun y=> P (Y:=Y) y i) 0:= ((contDiffAt_pi.mp hx) i).differentiableAt (by simp); have hy : DifferentiableAt ℝ (fun y=> P (Y:=Y') y i) 0:=((contDiffAt_pi.mp hv) i).differentiableAt (by simp)
    change fderiv ℝ (fun y=>P (Y:=Y) y i-P (Y:=Y') y i) 0 _=_; rw[fderiv_fun_sub hu hy];rfl
lemma cooler(G:Gauge):∃ D:ℝ,0≤D∧∀ (n:Side)(Y Y':Gal G n),Y ∈ rains G n→Y'∈rains G n→∀ (o:Site n)(a A:ℝ),0 < a→0 ≤ A→ Estate o (bottom (Y-Y')) a (fun _=>A)→
    let c:=a/5/4/5; Pet Prod.fst o (lush Y ∘ input G n-lush Y' ∘input G n) c (D*A*countCost c) 2:=by
    obtain ⟨D,hD,H⟩:=pipe_w G 3
    refine ⟨D*Fintype.card (Loc G 1),by positivity,fun n Y V hY hV o a A ha hA hp=>?_⟩
    intro c; let F:=Y-V; have he: F∈rains G n:= (rains G n).sub_mem hY hV; have ht:Cloaked F:= he.1; have hc:0 < c:=by unfold c; positivity
    have hm := H n F o A (a/5) (by positivity) hA ht (fun j=>pea_rain he hp hA ha.le j)
    have hx:PetW o (tidal F ∘ input G n) c (D*A) 2:=by
        refine tidal_pay (m:=2) (C:=D*A) (o:=o) (α:=c) ht ?_; intro i; have hv:= hm i; rwa[show a/5/((↑(3:ℕ):ℝ)+1)/((↑(3:ℕ):ℝ)+2)=c by unfold c; norm_num] at hv
    have hz := pet_lush o hx hc (by positivity)
    rw [mul_right_comm D]; exact hz.grows (lush_minus hY.1 hV.1)
-- linear of Mol and Holt
lemma beach (J:Acr G n→ℝ)(T:Fin 2→Loc G 1)(hf:ContDiffAt ℝ ω F 0)(hg: ContDiffAt ℝ ω H 0) (o:Site n): molt o T (F-H)=molt o T F -molt o T H:=by
    funext x; unfold molt vase; simp only[Pi.sub_apply]; rw[← sum_sub_distrib]; apply sum_congr rfl fun i _=>?_ ; unfold entry; rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top),_root_.sub_apply]; push_cast; ring
lemma drift_m (t:Fin 2→Loc G 1)(F:Maze G n)(o:Site n)(h:ContDiffAt ℝ ω F 0): ContDiffAt ℝ ω (molt o t F) 0:=by
    let p(j:ℕ)(i:Fin j→Lines G n 1):ℝ:=‖entry F 0 i‖*Real.exp (spanSites Prod.fst o i); let D(j:ℕ):=∑ i,p j i; let C:=∑ i∈range 3,D i
    have hb(i):0≤ D i:=sum_nonneg fun i _=> mul_nonneg (norm_nonneg _) (Real.exp_pos _).le; have hp:0 ≤ C:=sum_nonneg fun i _=> hb _; have hv: Pet Prod.fst o F 1 C 2:=by
       refine ⟨h,fun j hj i=>?_⟩; rw[neg_mul,one_mul,Real.exp_neg,← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
       exact (single_le_sum (s:=univ) (f:=p j) (fun i _=>mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (mem_univ i)).trans (single_le_sum (s:=range 3) (f:=D) (fun i _=>hb _) (mem_range.mpr (by omega)))
    exact (malt hv zero_lt_one hp t 0 3).analytic
lemma cuvee (d:ℕ)(z:Land)(i:Fin 2→Loc G 1)(hf:ContDiffAt ℝ ω F 0)(hh:ContDiffAt ℝ ω H 0): neap d (molt 0 i (F-H)) 0 z= neap d (molt 0 i F) 0 z- neap d (molt 0 i H) 0 z:=by unfold neap; rw [beach (fun _=>0) _ hf hh,iteratedFDeriv_sub_apply ((drift_m i F 0 hf).of_le le_top) ((drift_m i H 0 hh).of_le le_top),_root_.sub_apply, smul_sub]
variable (b:G.ColorIndex)
lemma suite_minus {X Y:Axis→ Maze G n}(h:∀ i,ContDiffAt ℝ ω (X i) 0)(hp:∀ i,ContDiffAt ℝ ω (Y i) 0): Holt b (X-Y)=Holt b X - Holt b Y:=by
    let A(v:Axis→Maze G n)(d i:Axis):=∑ p:Axis, pia d i b p (v p)
    have hx : crest b (X-Y)=crest b X-crest b Y:=by
        unfold crest suite; rw [← Finset.sum_sub_distrib]; apply sum_congr rfl fun i _=>?_ ; rw[← sum_sub_distrib]; apply sum_congr rfl fun j _=>?_ ; split; swap
        rw [← sum_sub_distrib]; refine Finset.sum_congr rfl fun k _ => ?_ ; unfold pia; rw [← map_sub Deb]; apply congr_arg; funext y; exact cuvee _ _ _ (h k) (hp k)
        rw[sub_zero]
    unfold Holt; rw[hx]; rw[sub_sub_sub_comm (crest b X)]; apply congr_arg; rw [←mul_sub]; apply congr_arg; unfold suite; rw[← sum_sub_distrib]; apply sum_congr rfl fun i _=> ?_;rw [← sum_sub_distrib]; apply sum_congr rfl fun j _=>?_ ; split; · rw[sub_zero]
    exact cuvee _ _ _ (h j) (hp j)
-- primitive linear price for hero.Leg.
private lemma payer{f:ℤ→ℂ}{X:ℤ→ℝ}(h:∀ i,‖f i‖ ≤ X i) : ‖FlopZ f‖ ≤ X 1 + X (-1) + X 2 + X (-2) :=by
   have hx (i): 0 ≤ X i:=(norm_nonneg _).trans (h i); let g:= f 1-f (-1);let x:= f 2-f (-2)
   rw [flopi,norm_mul]; refine le_trans (mul_le_mul_of_nonneg_left (norm_sub_le ..) (norm_nonneg _)) ?_; norm_num [norm_mul]; have hZ:= (norm_sub_le .. |>.trans (add_le_add (h 1) (h (-1)))); have hY:= (norm_sub_le .. |>.trans (add_le_add (h 2) (h (-2)))); linarith only [hZ,hY,hx 1,hx (-1),hx 2,hx (-2)]
private lemma panic{f:ℤ→ℂ}{X:ℤ→ℝ}(h:∀ i,‖f i‖ ≤ X i): ‖PanZ f‖ ≤ X 1+ X 0+ X (-1):=by
    have hx(i):0≤ X i:= (norm_nonneg _).trans (h i); rw[pani,norm_mul]; refine (mul_le_mul_of_nonneg_left (norm_add_le ..) (norm_nonneg _)).trans ?_; norm_num [norm_mul]
    have hv:= norm_sub_le (f 1) ((2:ℂ)*f 0); rw[norm_mul] at hv; norm_num at hv; linarith only[h 0,h 1,h (-1),hv,hx 1,hx 0,hx (-1)]
private lemma box_pe (g:Dish→ℝ)(hg:∀ i,0 ≤ g i) :∃ T:ℝ,0≤ T∧∀ (c:ℝ)(f :Dish→ℂ),(∀ i, ‖f i‖≤g i*c)→ ‖Deb f‖≤T*c:=by
    let V(x:ℤ):= g (x,1)+g (x,-1)+g (x,2)+g (x,-2)
    have hv x:0≤ V x:=add_nonneg (add_nonneg (add_nonneg (hg _) (hg _)) (hg _)) (hg _)
    refine ⟨V 1+V 0+ V (-1),add_nonneg (add_nonneg (hv _) (hv _)) (hv _),fun c f h=>?_⟩
    change ‖Complex.I*PanZ _‖≤ _; rw[norm_mul,Complex.norm_I,one_mul,add_mul,add_mul]; refine panic (X:=fun x=> V x*c) ?_; intro i; unfold V; simp only[add_mul]; exact payer (X:=fun j=>g (i,j)*c) (fun j=> h (i,j))
private lemma coach {X:Axis→ Axis→ ℂ}{Y:Axis→ Axis→ ℝ}{c:ℝ}(hg:0≤c)(hy:∀ d i,0 ≤ Y d i)(h:∀ i j, ‖X i j‖ ≤ Y i j*c): ‖suite X‖ ≤ (∑ i:Axis,∑ j:Axis,Y i j)*c:=by unfold suite; apply (norm_sum_le ..).trans; rw[Finset.sum_mul]; refine sum_le_sum fun i _ => (norm_sum_le ..).trans ?_; rw [Finset.sum_mul]; refine sum_le_sum fun j _=>?_ ; split; rw[norm_zero]; exact mul_nonneg (hy i j) hg; exact h i j
lemma WiltsPay : ∃ T:ℝ,0≤ T ∧ ∀ (G:Gauge)(n:Side)(b:G.ColorIndex)(F:Axis→Maze G n)(a A:ℝ),0<a→0≤ A→ (∀ i,Pet Prod.fst (0:Site n) (F i) a A 2)→ ‖Holt b F‖ ≤ T * (ramt 3 (Fin 2) a +ramt 2 (Fin 2) a) * A:=by
    let W(d i:Axis)(x:Dish):=((3:ℕ).factorial:ℝ)⁻¹ *‖lawn d i x‖^ (3:ℕ)
    let V(d:Axis):=((2:ℕ).factorial:ℝ)⁻¹ *‖(![step d, -step d]:Land)‖^(2:ℕ)
    have hv(d):0≤ V d:=by unfold V; positivity
    choose T ht H using fun d i:Axis=>box_pe (W d i) (fun i=>by unfold W; positivity)
    let r(d i:Axis):=∑ j:Axis,T d j; let q:=∑ d:Axis,∑ i:Axis,r d i; let X:=‖(1/2:ℂ)‖*(∑ d:Axis,∑ _j:Axis,V d)
    have hr(d i:Axis):0≤ r d i:= sum_nonneg fun _ _=>ht ..; have hq : 0≤ q:= sum_nonneg fun i _=> sum_nonneg fun j _=>hr i j; have hX:0 ≤ X:=mul_nonneg (norm_nonneg _) (sum_nonneg fun i _=>sum_nonneg fun j _=>hv i)
    refine ⟨q+X,add_nonneg hq hX,fun G n b F a A ha hA hp=>?_⟩
    let L:=ramt 3 (Fin 2) a; let D:=ramt 2 (Fin 2) a; have hL:0≤ L:=ramt_n ha; have hD:0≤ D:=ramt_n ha
    unfold Holt; apply (norm_sub_le ..).trans; refine le_trans (b:=q*(L*A)+X*(D*A)) ?_ ?_
    · refine add_le_add ?_ ?_
      · apply coach (mul_nonneg hL hA) hr; intro i j; unfold r; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun k _=>H _ _ _ _ fun x=> ?_); refine (norm_neap (k:=3) (p:=lawn i k x) (malt (hp k) ha hA ![mood G j b,mood G j b] 0 3) le_rfl).trans_eq ?_; unfold W L; ring
      rw[norm_mul]; apply le_trans (b:=‖(1/2:ℂ)‖ * ((∑ d:Axis,∑ _i:Axis,V d)*(D*A))) _ (by unfold X; apply le_of_eq; ring)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply coach (Y:=fun d _=>V d) (mul_nonneg hD hA) (fun i _=>hv _); intro d i; apply (norm_neap (k:=2) (p:=(![step d,-step d]:Land)) (malt (hp i) ha hA (![mood G i b,mood G i b]) 0 2) le_rfl).trans_eq; unfold V D;ring
    change _ ≤ (q+X)*(L+D)*A; linarith only [mul_nonneg hX (mul_nonneg hL hA),mul_nonneg hq (mul_nonneg hD hA)]
end YM.Trace.Xo
