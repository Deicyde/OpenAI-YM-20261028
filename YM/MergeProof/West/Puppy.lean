import YM.MergeProof.West.Geo
import YM.MergeProof.West.Peak
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around Accent Ribbons
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{n:ℕ}(W:DiffPlan S)
variable (hC:C.Makes)(hq:Cells.CellHyp C F)(ho:F.PointLimits C S)(H:S.Hierarchy)
variable {I:Watch C}(x:E4)(a:ℝ)(q:S.Tag)(b:Axis)
def trek (W:DiffPlan S) (b:Axis)(q:S.Tag):ℕ→ S.Tag
 | 0=>q
 | k+1 => Ward.rise W b (trek W b q k)
lemma trek_h (i:ℕ): (trek W b q i).1=q.1+i:=by
   induction i with
   | zero=>rfl
   | succ i ih=>dsimp [trek,Ward.rise];rw [ih]; omega
set_option quotPrecheck false
local notation "R" => fun i:ℕ=> fuga C.path.levels (i+1)
include H
lemma pelts (hp:W.Derivatives S)(y:Points n)(w:Fin n→ S.Tag)(t:ℝ) (hv:Points.cons (chord b x a t) y∈conf _) (i:ℕ):
   HasDerivAt (fun u:ℝ=>(a^i:ℝ) • disc (Fin.cons (trek W b q i) w) (Points.cons (chord b x a u) y))
      ((a^(i+1):ℝ) • disc (Fin.cons (trek W b q (i+1)) w) (Points.cons (chord b x a t) y)) t:=by
   let K:= trek W b q i; let u:= Points.cons (chord b x a t) y
   have hx : HasDerivAt (fun v:ℝ=> v*a) a t:=by simpa using (hasDerivAt_id' t).mul_const a
   have hh:= (cont_disc H (Fin.cons K w) hv).differentiableAt (by simp)
   have ht: Analysis.D (Points.direction 0 b) (disc (Fin.cons K w)) u=disc (Fin.cons (trek W b q (i+1)) w) u:=by
       have he: disc (Fin.cons (trek W b q (i+1)) w) u= disc (update (Fin.cons K w) 0 (Ward.rise W b ((Fin.cons (α:=fun _=>S.Tag) K w) 0))) u:=by
          rw [show update _ _ _=Fin.cons (α:=fun _=> S.Tag) (trek W b q (i+1)) w from ?_]
          funext i;refine Fin.cases ?_ (fun i=>?_) i
          · simp [K,trek]; -- maybe LOOP
          simp
       rw [he]; exact (fromD W H hp (x:=u) hv 0 b _)
   have hQ : HasDerivAt (fun v:ℝ=>disc (Fin.cons K w) (Points.cons (Ward.inc b x v) y)) (disc (Fin.cons (trek W b q (i+1)) w) u) (t*a):=by
       rw [← ht]; exact hh.hasFDerivAt.comp_hasDerivAt (t*a) (forwards b x y (t*a))
   rw [pow_succ, ← smul_smul]; exact (hQ.scomp t hx).const_smul (a^i)
include hC ho hq
variable {ι:Type*}[Fintype ι](X:ι→Watch C) (w: (i:ι)→Fin ((X i).n+1)→ S.Tag) (g:ι→ℂ)
def district (B:ℕ)(m:ℕ)(y:E4):ℂ:=∑ i:ι, g i * (((R) m:ℂ)^B * disc (Fin.cons q (w i)) (Points.cons y (X i).held))
lemma mountain (he:Note C.S (R) (-1))(hp:W.Derivatives S)(j:ℕ→ℕ)(s:ℝ)(hs:1<s) (hj:Tendsto j atTop atTop) (hJ:Tendsto (fun i:ℕ=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 s))(B:ℕ): ∃ D:ℕ, ∀ ε:ℝ,0<ε→∀ᶠ m in atTop,∀ j':Axis,∀ x:E4,(∀ t∈Icc (-arm D) (arm D), chord j' x (C.S.a (j m)) t∈ arena ((R) m))→
    ∃ z: ℕ→ℝ→ℂ, z 0=district q X w g B m ∘ chord j' x (C.S.a (j m)) ∧ (∀ i<D,∀ t∈Icc (-arm D) (arm D),HasDerivAt (z i) (z (i+1) t) t) ∧ ∀ t∈Icc (-arm D) (arm D), ‖z D t‖ ≤ ε :=by
   let L(i:ι):ℝ:=q.fst+2+(Clouds (expose∘w i):ℝ); let I: Filter ℕ:= atTop
   have hw:Tendsto (fun i:ℕ=>(i:ℝ)*(s-1)) I atTop:= Tendsto.atTop_mul_const (sub_pos.mpr hs) tendsto_natCast_atTop_atTop
   obtain ⟨D,hD⟩:= (eventually_all.mpr fun i=> hw.eventually_gt_atTop (L i)).exists
   refine ⟨D,fun ε hε=>?_⟩
   let Z:ℝ:=∑ i, ‖g i‖;have hZ:0≤Z:= Finset.sum_nonneg fun i _=> norm_nonneg _
   let M:ℝ:=ε/(Z+1); have hM:0<M:= div_pos hε (by linarith)
   have hh (i:ι)(j':Axis): ((trek W j' q D).fst:ℝ)+2+ (Clouds (expose∘ w i):ℝ) < (D:ℝ)*s:=by rw [trek_h,Nat.cast_add]; specialize hD i; unfold L at hD; linarith
   filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun v=> beneath (X i) (w i) (trek W v q D) D he hC hq ho H s j hj hJ (hh i v) hM,eventually_all.mpr fun i=>insideW (X i) he,(he.thins (by norm_num)).eventually (ge_mem_nhds (show (0:ℝ) < 1 from zero_lt_one))] with m hm hc h' j' x hx
   let a:= C.S.a (j m); let he':=(↑((R) m):ℂ)^B
   let F (i:ι)(k:ℕ)(t:ℝ):ℂ:= a^k • disc (Fin.cons (trek W j' q k) (w i)) (Points.cons (chord j' x a t) (X i).held)
   let f(k:ℕ)(t:ℝ):=∑ i:ι, (g i * he') * F i k t
   refine ⟨f,funext (fun t=> by simp [f,F,pow_zero,district,trek,mul_assoc,he',a]),fun k hk t ht=>?_,fun t ht=>?_⟩
   · exact HasDerivAt.fun_sum (fun i (_:i∈(Finset.univ:Finset ι))=> (pelts W H x a q j' hp (X i).held (w i) t (slide_conf C.S _ (hc i _ (hx t ht))) k).const_smul (g i*he'))
   have hf (i:ι): ‖F i D t‖ ≤ M:=by
       dsimp only [F]; rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos (j m)).le D)]; exact hm i j' _ (hx t ht)
   apply (norm_sum_le ..).trans
   calc
       _ ≤ ∑ i:ι, ‖g i‖ * M:= Finset.sum_le_sum (fun i _=> by
         rw [norm_mul,norm_mul]; refine mul_le_mul (show ‖g i‖*‖he'‖≤ ‖g i‖ from mul_le_of_le_one_right (norm_nonneg _) (?_)) (hf i) (norm_nonneg _) (norm_nonneg _); rw [show he'=_ from rfl,norm_pow]; exact pow_le_one₀ (norm_nonneg _) (by rw [Complex.norm_real,Real.norm_of_nonneg (he.pos m).le]; exact h'))
       _ = Z*M:= (Finset.sum_mul ..).symm
       _ ≤ ε:= (mul_le_mul_of_nonneg_right (show Z ≤ (Z+1) by linarith) hM.le).trans_eq (mul_div_cancel₀ _ (by linarith : Z+1≠0))
end YM.MergeProof.Acme
