import YM.RG08.Vale.Rivet
/-!
# Pre-length offsets and all rates, exponential and polynomial
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open Function Filter Matrix Lattice Bloch Exterior Precision Laurent Next.Free Work.F08 RG
open Quire Shade Planned.PrimaryIntegral295 Push.AbsoluteSums Finset
open scoped Topology ContDiff Classical BigOperators
variable {d n u:ℕ} {α β:Type} [Fintype β]{L:Side}{A B C w σ:ℝ} {Q:Cross L α β}{p:Cover×α→ℝ}{q:Cover×β→ℝ}
lemma dime_polExp (w:ℝ) (h :0<w) (d:ℕ):∃ B:ℝ,0≤B∧∀ x:Cover,dime d x *Real.exp (w/2*size x) ≤ B*Real.exp (w*size x) := by
  let t:= w/2; have he:0<t:=half_pos h
  let B:=t⁻¹^d*(d.factorial:ℝ)*Real.exp t
  have hB:0≤B:= by unfold B; positivity
  refine ⟨B,hB,fun x=>?_⟩
  have hh : dime d x ≤ B*Real.exp (t*size x) := by apply le_trans (polynomial_price he (show 0 ≤ 1+(size x:ℝ) by positivity) d); unfold B; rw [mul_add,mul_one,Real.exp_add]; linarith
  refine (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq ?_
  rw [mul_assoc,← Real.exp_add,show t*↑(size x)+ (w/2)*↑(size x) = w*size x from by unfold t; ring]
lemma expGrowth (d:ℕ)(hw:0<w)(hv:0<σ)(hV:σ≤A)(hz:0≤B):∃ C:ℝ,1≤C∧ ∀ (L:Side)(Q:Cross L α β), σ ≤ L.val*w/2 → PaysPath Q A B d→ TakesP Q (plyH w) (plyH σ) d C := by
  obtain ⟨K,hK,H⟩:= dime_polExp w hw d
  let f:=(Fintype.card β:ℝ)*B; have hf : 0 ≤ f := by unfold f; positivity
  let v:=Real.exp (5*σ)*f; have hh: 0≤v := by unfold v; positivity
  let t:= v*K; have ht:0≤t:= by unfold t; positivity
  let P:=1+K+v+t; have hP:1≤P:= by unfold P; linarith
  have he':K≤P:= by unfold P; linarith
  have hA:v≤P:= by unfold P; linarith
  have ht':t≤P:= by unfold P; linarith
  refine ⟨P,hP,fun L Q hc h=> ⟨plyH_one hw.le,plyH_one hv.le,fun x=>?_,fun X l hl i x hX=>?_,fun X x hX=>?_⟩⟩
  · exact (le_mul_of_one_le_right (Carrier.liftCost_pos ..) (show 1≤Real.exp (w/2*size x.1) from Real.one_le_exp (by positivity))).trans ((H x.1).trans (mul_le_mul_of_nonneg_right he' (Real.exp_pos ..).le))
  · simp_rw [foams h.odd]; apply Ink.raise (nodeExp (h.offsets l hl) hv.le hV X (x,i)); have hm : (L.val:ℝ)>0:= by positivity
    have hy : (L.val:ℝ)⁻¹ * size x ≤ 1:= (mul_le_mul_of_nonneg_left (show (size x:ℝ) ≤ _ from Nat.cast_le.mpr hX) (by positivity)).trans_eq (inv_mul_cancel₀ hm.ne')
    let k:=l.length+1
    calc
      _ ≤ Real.exp (5*σ)*((Fintype.card β:ℝ)*(B*height L k)) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (mul_nonneg (by positivity) (mul_nonneg hz (height_p ..).le))
      _ = v * height L k := by unfold v f; ring
      _ ≤ _:= by apply mul_le_mul_of_nonneg_right hA (height_p ..).le
  apply Ink.raise (nodeExp (h.offsets [] (by simp)) hv.le hV X x)
  let m:=(L.val:ℝ); have hm:0<m:= by unfold m; positivity
  let R:=Real.exp (w*size x.1)
  let J:=Real.exp (w/2*size x.1)
  have HJ:0≤J:= (Real.exp_pos _).le
  have hM:σ*m⁻¹ ≤ w/2:= by rw [←div_eq_mul_inv]; apply (div_le_iff₀ hm).2; linarith
  calc
    _ ≤ (Real.exp (5*σ)*J)*(f*m⁻¹) := by
      change Real.exp (σ*(4+m⁻¹*size x.1)) * ((Fintype.card β:ℝ)*(B*m⁻¹^1))≤ _; rw [pow_one,← mul_assoc (Fintype.card β :ℝ) B]; unfold J; rw [← Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hM (show 0≤(size x.1:ℝ) by positivity),hv])) (show 0 ≤ f*m⁻¹ by positivity)
    _ = v*m⁻¹ * (1*J) := by unfold v; ring
    _ ≤ v*m⁻¹ * ((height L d*dime d x.1)*J) := by apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (height_ge _ hX _) HJ); positivity
    _ ≤ t*height L (d+1)*R := by
      have he:= mul_le_mul_of_nonneg_left (H x.1) (show 0 ≤ v*height L (d+1) from mul_nonneg hh (height_p ..).le)
      unfold height t m J R at *; rw [pow_succ] at he ⊢; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' (height_p ..).le) (Real.exp_pos ..).le

omit [Fintype β] in
def bud (k:ℕ)(p: Site L)(Q:Cross L α β) : Paper α β := fun x y=> Trellis.sector k (fun z=> node p Q (z,x.2) y) (Place.seat x.1)
omit [Fintype β] in
def remain (k:ℕ)(p: Site L)(Q:Cross L α β) : Paper α β := fun x y=> Trellis.surplus (fun z=> node p Q (z,x.2) y) k x.1
lemma buds_bound (q:Cover×β→ℝ)(he:1≤q) (d k : ℕ)(hk:k≤d):∃ P:ℝ,1≤P∧ ∀ (L:Side)(Q: Cross L α β) (C:ℝ) (p:Cover×α→ℝ), TakesP Q p q d C → 0≤C→ ∀ x y,
    Charge q (bud k x Q y) (P*C* height L (k+1)* dime k y.1) := by
  obtain ⟨D,hD,H⟩:= sectors_paid (v:=q) (zero_le_one.trans he) k
  refine ⟨_,hD,fun L Q C p h hc x y=>?_⟩; rw [mul_assoc D C]
  exact H _ (fun z g=> node x Q (g,y.2) z) (mul_nonneg hc (height_p ..).le) (fun l hl=> hl ▸  (h.main_bound x l (by omega) y.2 0 (by simp [size]) )) _ -- change proof
omit [Fintype β] in
lemma buds_sum (k:ℕ)(t:Site L)(Q:Cross L α β)(x:Cover×α): node t Q x=(∑ i∈range k, bud i t Q x)+remain k t Q x := by
  funext y; unfold remain bud Trellis.surplus Trellis.fitting; rw [Pi.add_apply,Pi.sub_apply,Finset.sum_apply]; abel
lemma savings (he:1≤q)(d:ℕ)(hc:1≤C): ∃ P:ℝ,1≤P∧ ∀ (L:Side)(Q:Cross L α β), TakesP Q p q d C→ ∀ x y,
    (∀ i<d,Charge q (bud i x Q y) (P*height L (i+1)*p y)) ∧ Charge q (remain d x Q y) (P*height L (d+1)*p y) := by
  classical
  choose K hK H using fun i: Fin (d+1)=> buds_bound (α:=α) q he d i.val (Nat.le_of_lt_succ i.isLt)
  let A:= ∑ i,K i; have ha: ∀ i, K i ≤ A:= fun i=> single_le_sum (fun j _=>zero_le_one.trans (hK j)) (mem_univ i)
  have hA := (hK 0).trans (ha 0); let V := A*C*C; let P:= (C+C*C)+((d:ℝ)+1)*V
  have hC:0≤C:= zero_le_one.trans hc; have hV:1≤V:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hc) hc
  have he1:0≤(d:ℝ)*V:= by positivity
  have he2:0≤C*C:= by positivity
  have hu:P=C+C*C+((d:ℝ)*V+V):= by unfold P; ring
  have hp:1≤P:= by linarith
  have hT:V≤P:= by linarith
  have ho:C*C≤P:= by linarith
  refine ⟨P,hp,fun L Q h x y=> ⟨fun i hi=> ?_, ?_⟩⟩
  · let m:Fin (d+1):=⟨i,by omega⟩
    refine Ink.raise (H m L Q C p h hC x y) ?_
    calc
      _ ≤ A*C*height L (i+1)*(C*p y) := by
        apply mul_le_mul _ ((dime_more hi.le y.1).trans (h.size_bound y)) (Carrier.liftCost_pos ..) _
        · apply mul_le_mul_of_nonneg_right _ (height_p ..).le; exact mul_le_mul_of_nonneg_right (ha m) hC
        exact mul_nonneg (mul_nonneg (zero_le_one.trans hA) hC) (height_p ..).le
      _ = V*height L (i+1)*p y := by unfold V; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT (height_p ..).le) ((h.first y).trans' zero_le_one)
  rcases le_total (size y.1) L.val with hx|hx
  · let F:= fun k' z=>node x Q (z,y.2) k'
    let W:=height L (d+1); have hw:0≤W:= (height_p ..).le
    apply Ink.raise (surplus_paid (zero_le_one.trans he) d L.val F (show 0≤ C*height L (d+1) by positivity) (fun l hl k hk=> hl ▸ h.main_bound x l hl.le y.2 k hk) y.1 hx)
    calc
      _ ≤ C*W*(C*p y) := by
        refine mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) (show (size y.1:ℝ) ≤1+ size y.1 from le_add_of_nonneg_left zero_le_one) d).trans (h.size_bound _)) (mul_nonneg hC hw)
      _ = C*C*W*p y := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ho hw) ((h.first y).trans' zero_le_one)
  · have hv i (ht : i∈range d): Charge q (bud i x Q y) (V * height L (d+1)*p y) := by
      let m:Fin (d+1):=⟨i,by simp only [mem_range] at ht; omega⟩
      apply Ink.raise (H m L Q C p h hC x y); have hp : i+ (d-i)=d:= Nat.add_sub_of_le (mem_range.mp ht|>.le)
      have hh:= height_ge L hx (d-i)
      have hO : height L (i+1)*dime i y.1 ≤ height L (d+1)*dime d y.1 := by
        calc _ ≤ (height L (i+1)*dime i y.1)*(height L (d-i)*dime (d-i) y.1) := le_mul_of_one_le_right (mul_nonneg (height_p ..).le (Carrier.liftCost_pos ..)) hh
             _ = _ := by rw [mul_mul_mul_comm]; unfold height dime Carrier.liftCost; rw [←pow_add,← pow_add,show i+1+(d-i)=d+1 by omega,hp]
      change K m*C*height L (i+1)*_≤_
      calc
        _ ≤ K m*C*(height L (d+1)*(C*p y)) := by rw [mul_assoc]; refine mul_le_mul_of_nonneg_left (hO.trans (mul_le_mul_of_nonneg_left (h.size_bound y) (height_p ..).le)) (mul_nonneg (zero_le_one.trans (hK _)) hC)
        _ ≤ _ := by apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ha m) hC) (show 0 ≤ height L (d+1)*(C*p y) from mul_nonneg (height_p ..).le (mul_nonneg hC ((h.first y).trans' zero_le_one)))) (le_of_eq ?_); unfold V; ring
    rw [show remain d x Q y=node x Q y-∑ j∈range d,bud j x Q y from by rw [buds_sum d]; abel]; apply Ink.raise (Charge.sub (h.far_bound x y hx) (Charge.sums (zero_le_one.trans he) hv) (zero_le_one.trans he)); rw [sum_const,card_range,nsmul_eq_mul]
    have hv : C+(d:ℝ)*V ≤ P := by linarith
    apply le_trans (le_of_eq (show _=(C+(d:ℝ)*V)*(height L (d+1)*p y) from by ring)) ((mul_le_mul_of_nonneg_right hv (mul_nonneg (height_p ..).le ((h.first y).trans' zero_le_one))).trans_eq (mul_assoc ..).symm)
end YM.RG08.Vale
