import YM.Next.RANK.Headwater
import YM.Next.RANK.Porter

/-! Exact path tail in kept change. windings cost true lengths then summation.
    Costs exposed; no exp(-B) to forcedAllowance! -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p q : BudgetPoint} {r : ℕ}
variable {c : Clip} {t τ μ A σ Λ : ℝ}
variable (P : PathData G)

def valExtent (p : PlaqAxes) (i j : ℕ) (r : ℕ) (n : Side) := halo (n:=n) (2*r) {0}∪ lives (0 : Site n) (P.row p i).2∪ lives 0 (P.row p j).2

def Long (p : PlaqAxes) (i j : ℕ) (r) := ¬ ((P.row p i).2.length ≤ r ∧ (P.row p j).2.length ≤r)

def Bal (a : PlaqAxes) (i j : ℕ) (r : ℕ) (c : Clip) (t τ : ℝ) (U : Config G n) := if Long P a i j r then
    dam c t τ U * inner ℝ (P.ellTerms (0,a) i U) (P.ellTerms (0,a) j U)/2 else 0

lemma lap_basis (a : PlaqAxes) i j (H : Long P a i j r) : r ≤ (P.row a i).2.length + (P.row a j).2.length:= by unfold Long at H; omega
lemma lap_mark (a : PlaqAxes) (i j r) : 0 ∈ valExtent P a i j r n:= mem_union_left _ (mem_union_right _ (starts ..))

private lemma wrap_cost (w : Slot) (b : ℕ) (hb : 0<b) (n : Side) :
    b*coverNumber b (lives (0:Site n) w) ≤ 100000*(b+w.length+1) := by
  let X:= lives (0:Site n) w
  apply (Nat.mul_le_mul_left b (cover_mono (halo_subset 0 X) b)).trans
  apply (widen 1 b 0 (by norm_num) hb (by omega) _).trans
  rw [one_mul,Nat.add_assoc]; gcongr; exact qualifies ..

lemma visit_price (p) (i j) (r : ℕ) (h : 0<r) : r * coverNumber r (valExtent P p i j r n)≤
    500000*(r+(P.row p i).2.length+(P.row p j).2.length) := by
  let a:= (P.row p i).2;let b:= (P.row p j).2;let o:= (0:Site n); let X:= lives o a; let Y:= lives o b;let Z:= halo (2*r) {o}
  have hp := meets_sum (show o∈ Z∪X from mem_union_right _ (starts o a)) (starts o b) r
  have hz: o∈ Z:= halo_subset _ _ (mem_singleton_self _)
  have hy:= meets_sum hz (starts o a) r
  have he := tile o 2 _ h
  apply le_trans (Nat.mul_le_mul_left r (le_trans hp (Nat.add_le_add_right (le_trans hy (Nat.add_le_add_right he _)) _))) _
  simp only [mul_add]; apply le_trans (Nat.add_le_add (Nat.add_le_add_left (wrap_cost a r h n) _) (wrap_cost b r h n)) _
  norm_num at *; nlinarith only [h]

lemma bal_budget (h : P.Bounds c σ μ Λ) (x i j) (r : ℕ) (hr : 0<r) {e : ℝ} (he : 0≤e) (hq : (2000000:ℝ)*e ≤ σ * r) (H : Long P x i j r) :
    |(P.row x i).1| * |(P.row x j).1| * debt r e (valExtent P x i j r n) ≤
      |(P.row x i).1| * Real.exp (σ * (P.row x i).2.length) * (|(P.row x j).1| * Real.exp (σ * (P.row x j).2.length)) * Real.exp (-σ / 4*r) := by
  let a := (P.row x i).2; let b := (P.row x j).2; let m:= valExtent P x i j r n
  let F : ℝ := r; let A : ℝ:= a.length;let B : ℝ:= b.length
  have ha : (r:ℝ)≤ A+B := by unfold A B; exact_mod_cast lap_basis P x i j H
  have hs : F*(coverNumber r m : ℝ)≤ 500000*(F+A+B) := by dsimp only [F,A,B,a,b,m]; exact_mod_cast visit_price (n:=n) P x i j r hr
  have hb := mul_le_mul_of_nonneg_right hq (show 0 ≤ F+A+B by unfold A B F; positivity)
  have hz : debt r e m ≤ Real.exp (σ * A) * Real.exp (σ*B) * Real.exp (-σ/4*r) := by
    unfold debt; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr
    have hf : 0 < F := by unfold F; exact_mod_cast hr
    apply le_of_mul_le_mul_left _ hf
    have hp:σ*F*F≤ σ*F*(A+B):= mul_le_mul_of_nonneg_left ha (mul_nonneg h.width.le hf.le)
    dsimp only [F] at *; linarith only [hb, mul_le_mul_of_nonneg_left hs he,hp, mul_nonneg (mul_nonneg h.width.le hf.le) hf.le]
  apply (mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq;dsimp only [A,B,a,b]; ring

lemma paid_Bal (i j x c U) : |Bal P x i j r c t τ U (n:=n)| ≤ 2* |(P.row x i).1| * |(P.row x j).1| := by
  unfold Bal; split
  · rw [abs_div,abs_mul]; rw [abs_of_nonneg (dam_sign _|>.1)]
    have h (k : ℕ) : ‖P.ellTerms (0,x) k U‖≤ |(P.row x k).1| * 2 := by rw [ellTerms,norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)
    have hh:=(abs_real_inner_le_norm (P.ellTerms (0,x) i U) _).trans (mul_le_mul (h i) (h j) (norm_nonneg _) (by positivity))
    norm_num
    linarith only [mul_le_mul (show dam c t τ U ≤ 1 from dam_sign U|>.2) hh (abs_nonneg _) zero_le_one]
  rw [abs_zero]; positivity

-- Worm with footprint even if address unused
variable (hv : Turnon c τ r) (hp : τ ≤ t) (hq : 8≤r) (hu : 0<τ)

def worm (i : PlaqAxes×ℕ×ℕ) : Wickless G n τ where
  extent:=valExtent P i.1 i.2.1 i.2.2 r n
  active:=⟨0,lap_mark ..⟩
  value U:=Bal P i.1 i.2.1 i.2.2 r c t τ U
  inv k U:= by
    unfold Bal; simp only;split
    · rw [dam_gauge k U, steam P _ _ U k, steam P _ _ U k]; congr 2
      let f : G.Color →ₗᵢ[ℝ] G.Color := { G.adjoint (k (0:Site n)) with norm_map' := G.norm_adjoint _}
      exact f.inner_map_map ..
    rfl
  meas:= by
    unfold Bal; split
    · apply (dam_meas.mul ..).div_const
      apply Continuous.measurable; unfold ellTerms Slot.atSite expandAt; fun_prop
    exact measurable_const
  sees U V h _:= by
    unfold Bal; simp only; split
    · rw [dam_leg hv hp hq hu U V (agrees_mono h (by exact fun x hx => mem_union_left _ (mem_union_left _ hx))), steamed P (0,i.1) i.2.1 U V (agrees_mono h (by exact fun x hx=>mem_union_left _ (mem_union_right _ hx))),
        steamed P (0,i.1) i.2.2 U V (agrees_mono h (by exact fun x hx=> mem_union_right _ hx))]
    rfl
  untouched U h:=by
    unfold Bal; split
    · rw [dam_zero _ hv hu U (Finset.disjoint_left.mpr fun x hx => Finset.disjoint_left.mp h (mem_union_left _ (mem_union_left _
        (halo_mono (show r ≤ 2*r by omega) (le_refl _) hx)))),zero_mul,zero_div]
    rfl

-- l² exact represented omitted row pairs with tails
private lemma gang (q : ℕ→ℝ) (h : ∀ i,0≤q i) (ht : Summable q): Summable (fun p : ℕ×ℕ=> q p.1*q p.2):=ht.mul_of_nonneg ht h h
private lemma bosom {X : ℕ → G.Color} (h : Summable X) (hp : Summable fun x=>‖X x‖) :
    Summable (fun p : ℕ×ℕ=> inner ℝ (X p.1) (X p.2)) ∧ ‖∑' i,X i‖^2=∑' p:ℕ×ℕ, inner ℝ (X p.1) (X p.2) := by
  let f:=fun p : ℕ×ℕ=>inner ℝ (X p.1) (X p.2)
  have hh:=gang _ (fun i=> norm_nonneg (X i)) hp
  have ht : Summable f := hh.of_norm_bounded (fun i=> abs_real_inner_le_norm ..)
  refine ⟨ht,?_⟩
  change _= ∑' i,f i; rw [ht.tsum_prod]
  have he (a : G.Color) : inner ℝ a (∑' i, X i)=∑' i,inner ℝ a (X i):= (innerSL ℝ a).map_tsum h
  rw [← real_inner_self_eq_norm_sq,he]; refine tsum_congr fun i=> ?_; rw [real_inner_comm (X i),he]

include hv hp hq hu in
lemma earning (h : P.Bounds c σ μ Λ) (V : Config G n) (he : p.threshold=t) (hV : q.threshold=τ) :
    baseGift P p q c V-basin P r c t τ V=∑' i, (worm P hv hp hq hu i).value V := by
  let T:=fun i=> (worm P hv hp hq hu i).value V
  let w:= dam c t τ V
  have hm (x) : Summable (fun i:ℕ×ℕ=> T (x,i)) ∧
      dam c p.threshold q.threshold V * ‖P.ell V (0,x)‖^2/2 - w * ‖lakeHead P r x V‖^2/2 = ∑' i:ℕ×ℕ,T (x,i):= by
    let f i:=P.ellTerms (0,x) i V;let g:=drip P r x V
    obtain ⟨ha,hf⟩:=bosom (G:=G) (X:=f) ((P.ell_dominated h _).summable _) ((P.ell_dominated h _).absolute _)
    have hh : Summable fun i=> ‖g i‖:= by
      refine ((P.ell_dominated h (0,x)).absolute V).of_nonneg_of_le (fun i=> norm_nonneg (g i)) ?_
      intro i; unfold g drip;split_ifs; exact le_rfl;rw [norm_zero]; positivity
    obtain ⟨ht,hg⟩:=bosom (G:=G) (X:=g) hh.of_norm hh
    let P1:=fun i:ℕ×ℕ=> inner ℝ (f i.1) (f i.2);let P2:=fun i:ℕ×ℕ=>inner ℝ (g i.1) (g i.2)
    let P3:=fun i=> w/2*(P1 i-P2 i)
    have h3 (i): T (x,i)=P3 i:= by
      unfold T P3; dsimp only [P1,P2,g,drip,worm,Bal]; simp only [Long]; unfold f w; split_ifs <;> first| tauto| (try simp only [inner_zero_left,inner_zero_right]); ring
    refine ⟨((ha.sub ht).mul_left (w/2)).congr fun i=> (h3 i).symm,?_⟩
    rw [he,hV]; change w*‖∑' i,f i‖^2/2 - w*‖∑' i,g i‖^2/2 = _
    simp_rw [h3]; rw [hf,hg]; unfold P3; rw [tsum_mul_left,Summable.tsum_sub ha ht]; ring
  refine Eq.trans ?_ ((slice_total (fun x=>fun i:ℕ×ℕ=> T (x,i)) (fun i=> (hm i).1)).2.symm); unfold baseGift basin; rw [← sum_sub_distrib]; exact sum_congr rfl fun i _=> (hm i).2

def outTail (σ μ : ℝ) (q : ℕ) : ℝ:= (Fintype.card PlaqAxes:ℝ)*2*μ^2*Real.exp (-σ/4*q)

include hv hp hq hu in
lemma tailing (h : P.Bounds c σ μ Λ) {e : ℝ} (he : 0≤e) (hq' : (2000000:ℝ)*e ≤ σ * r) (q : BudgetPoint) (hb : q.B=r) :
    Dial (worm P hv hp hq hu (n:=n)) q e (outTail σ μ r) := by
  let W := worm P hv hp hq hu (n:=n)
  let L := fun i:PlaqAxes×ℕ×ℕ=> if Long P i.1 i.2.1 i.2.2 r then 2*|(P.row i.1 i.2.1).1| *|(P.row i.1 i.2.2).1| else 0
  let Y:=fun i=> L i*debt r e (W i).extent
  have hz i:0≤ L i:= by unfold L; split<;>positivity
  have hB i : 0≤Y i:=mul_nonneg (hz _) (Real.exp_pos _).le
  let w:=Real.exp (-σ/4*r)
  have hQ (x : PlaqAxes) : Summable (fun i:ℕ×ℕ=>Y (x,i)) ∧ ∑' i:ℕ×ℕ, Y (x,i)≤2*μ^2*w:= by
    let g i:=|(P.row x i).1| * Real.exp (σ * (P.row x i).2.length)
    let f i:=Y (x,i)
    have hy (i): f i≤ (2*w)*(g i.1*g i.2):= by
      unfold f Y L; simp only; split_ifs with ht
      · have h₀ := bal_budget (n:=n) P h x i.1 i.2 r (by omega) he hq' ht
        dsimp only [W,w,g,worm]; linarith only [h₀]
      have h₁ : 0 ≤ g i.1 := (h.rows _).1 _; have h₂ : 0 ≤ g i.2 := (h.rows _).1 _
      rw [zero_mul]; dsimp only [w]; positivity
    have he : Summable g:= (h.rows _).2.1;have hg : Summable fun p : ℕ×ℕ=> g p.1*g p.2:= gang _ (h.rows _).1 he
    have hf : Summable f := (hg.mul_left (2*w)).of_nonneg_of_le (fun i=> hB _) hy
    refine ⟨hf,(hf.tsum_le_tsum hy (hg.mul_left _)).trans ?_⟩
    rw [tsum_mul_left,← he.tsum_mul_tsum he hg]; unfold w;rw [← sq, mul_right_comm]
    have hz : (∑' i,g i)^2 ≤ μ^2 := pow_le_pow_left₀ (tsum_nonneg (g:=g) (h.rows _).1) (h.rows _|>.2.2) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num)) (Real.exp_pos _).le
  have hT := slice_total (fun x=>fun j:ℕ×ℕ=> Y (x,j)) (fun x=> (hQ x).1)
  refine ⟨fun _=> lap_mark .., ⟨L,fun i=>⟨hz i, fun U=> ?_⟩,?_⟩⟩
  · unfold L; split
    · exact paid_Bal ..
    rename_i h; change |Bal P _ _ _ _ _ _ _ U| ≤ _; unfold Bal; simp only [h,↓reduceIte,abs_zero]
    exact le_rfl
  rw [hb]; refine ⟨hB,hT.1,hT.2.le.trans ?_⟩; apply (sum_le_sum fun x _=> (hQ _).2).trans; simp only [outTail,sum_const,nsmul_eq_mul,card_univ]; unfold w; linarith
end YM.Next.Rank.Alarm
