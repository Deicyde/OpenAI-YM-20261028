import YM.Extension.UV.Station.Momentum
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Function Filter Set Lattice Laurent Bloch Matrix Next.Free Metric Precision Exterior RG
open scoped Topology Classical BigOperators
variable {G:Gauge} {A:Levels G}
section currency
private def shapes := 1+(Fintype.card (TypeFace 1):ℝ)+(Fintype.card (TypeFace 2):ℝ)
private lemma shape_pos : 1≤ shapes := by unfold shapes; linarith [Nat.cast_nonneg (Fintype.card (TypeFace 1)) (α:=ℝ),Nat.cast_nonneg (Fintype.card (TypeFace 2)) (α:=ℝ)]
private lemma shape_one : (Fintype.card (TypeFace 1):ℝ) ≤ shapes := by unfold shapes; have hw := (Nat.cast_nonneg (α:=ℝ) (Fintype.card (TypeFace 2))); linarith
private lemma shape_two : (Fintype.card (TypeFace 2):ℝ) ≤ shapes := by unfold shapes; have hw := (Nat.cast_nonneg (α:=ℝ) (Fintype.card (TypeFace 1))); linarith

def stone (P:MapPrices) i:=shapes*(max 1 (1/P.α i))*(max 1 (P.Ω i))
lemma stone_one (P:MapPrices) i : 1 ≤ stone P i:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le shape_pos (le_max_left ..)) (le_max_left ..)
def grip (P:MapPrices) (A:Levels G) m:= stone P (A.clock.J m)*(stone P (A.clock.J (m+1)))^2
lemma stone_charge (P:MapPrices) i {c h F:ℝ} (hc:c ≤ shapes) (hc':0≤c) (hf:0≤F) (hh : 0≤h ∧ h ≤ max 1 (1/P.α i)):
    c*h*F*P.Ω i ≤ stone P i*F := by
  by_cases h':P.Ω i < 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hc' hh.1) hf) h'.le).trans (mul_nonneg (zero_le_one.trans (stone_one P i)) hf)
  exact le_trans (by have ha := hh.2; have hh0:=hh.1; have hh' := shape_pos; have hv := le_of_not_gt h';
                     gcongr; linarith [le_max_right 1 (1/P.α i),le_max_right 1 (P.Ω i)] : _ ≤ shapes*max 1 (1/P.α i)*F*max 1 (P.Ω i)) (by unfold stone; exact le_of_eq (by ring))
lemma stone_economy (P:MapPrices) i (b:ℝ) (v:ℕ) (hb:0<b) (e c h:ℝ) {F:ℝ} (he:e=P.Ω i/b^v) (hc:c ≤ shapes) (hc':0≤c) (hf:0≤F) (hh : 0≤h ∧ h ≤ max 1 (1/P.α i)):
    c*h*F*e ≤ stone P i*F/b^v := by rw [he,←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); exact stone_charge P i hc hc' hf hh
end currency
section step
variable (M:Horizon A) (P:MapPrices) {l} (hp:M.Suffices P) (hw:Present A M l)
    (heq : ∀ n m, m<n → (M.towers n m).T=((destination A n m).duo A.clock.kernel.penalty).T)
    (n m p : ℕ) (hn:m<n)
def plane : Matrix (Co (A.S.side (m+1) p) (TypeFace 1)) (Co (A.S.side m p) (TypeFace 1)) ℝ:= installed (A.clock.op m p).ratio (M.towers n m).A0
def guardK := installed (A.clock.op m p).ratio (M.towers n m).T
variable (F:Co (A.S.side m p) (TypeFace 2)→ℝ) {b:ℝ} (hb:0≤b)
include hp hn hb
lemma plane_lower (x : Body 1 (A.S.side m p) →ℝ) (hx : Bounded x b) : Bounded ((plane M n m p) *ᵥ x) ((stone P (A.clock.J (m+1)))*b/(((A.S.block m)).val:ℝ)):= by
   let i:=A.clock.J (m+1)
   have ht := (hp.costs _ _ hn).2.2.2 [] (show _ ≤ _ from Nat.zero_le _) |>.1
   have ht' := cross_bound (A.clock.op m p).ratio (M.towers n m).A0 x hb hx (P.alpha_pos i).le ht
   exact fun x=> (ht' x).trans (by simp only [List.length_nil,Nat.add_zero,pow_one,←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); rw [← mul_one (Fintype.card (TypeFace 1):ℝ)]; exact stone_charge P i shape_one (by positivity) hb ⟨zero_le_one,le_max_left ..⟩)
lemma guard_bound (hF:Bounded F b): Bounded ((guardK M n m p)*ᵥ F) ((stone P (A.clock.J (m+1)))*b/(((A.S.block m)).val:ℝ)^2):= by
   let i:=A.clock.J (m+1)
   have ht := (hp.costs _ _ hn).2.2.2 [] (show _ ≤ _ from Nat.zero_le _) |>.2
   have ht' := cross_bound (A.clock.op m p).ratio (M.towers n m).T F hb hF (P.alpha_pos i).le ht
   exact fun x=> (ht' x).trans (by simp only [List.length_nil,Nat.add_zero,←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); rw [← mul_one (Fintype.card (TypeFace 2):ℝ)]; exact stone_charge P i shape_two (by positivity) hb ⟨zero_le_one,le_max_left ..⟩)
include heq in
set_option maxHeartbeats 700000 in
lemma guard_varied_eq (hF:varied F b): varied ((guardK M n m p) *ᵥ F) ((stone P (A.clock.J (m+1)))*b/(((A.S.block m)).val:ℝ)^3) := by
   let j:=A.clock.J (m+1); have hj := P.alpha_pos j
   let q:= (A.clock.op m p).ratio; let T:=M.towers n m; let f' := ((guardK M n m p) *ᵥ F)
   have ht:=hp.costs _ _ hn
   have h4:= A.clock.adm (m+1)
   have hd (a:Axis) : (advanceC q.count T.T [a]).strip (P.α j) (P.Ω j /(q.count.val:ℝ)^3):=by exact (ht.2.2.2 [a] (by  simp; omega)).2
   have H a := cancel_entry q (advanceC q.count T.T [a]) F hb hF hj (hd a) (fun e=> by
      convert cancellation_eq M heq P hp m p n hn a e using 2
      all_goals first | rfl | (funext q'; split <;> simp_all))
   have hu a : installed q (advanceC q.count T.T [a])=motion (TypeFace 2) (A.S.side (m+1) p) [a]*installed q T.T := flow_movement q T.T [a] (A.S.block_odd m) (fun r hr=> by simp only [List.length_singleton] at hr; exact ⟨_,_,P.alpha_pos j,(ht.2.2.2 r (show _≤_ by  omega)).2⟩)
   have hx (s:Axis) (t:Site (A.S.side (m+1) p)) a: |f' (t+step s,a)-f' (t,a)| ≤ ((stone P j)*b/(((A.S.block m)).val:ℝ)^3):= by
      have he := H s (t,a); rw [hu,← mulVec_mulVec, kneel] at he; change |f' (t+step s,a)-f' (t,a)|≤_ at he
      apply he.trans (b:=(Fintype.card (TypeFace 2):ℝ)*(1/P.α j)*b*(P.Ω j/(((A.S.block m)).val:ℝ)^3)) ?_; rw [←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); exact stone_charge P j shape_two (by positivity) hb ⟨div_nonneg zero_le_one (P.alpha_pos j).le,le_max_right ..⟩
   rintro i a ⟨s,_|_⟩
   · simpa only [Step.vec,Bool.false_eq_true,if_false] using hx s i a
   simp only [Step.vec,if_true]
   have hx := hx s (i + -step s) a
   rw [add_assoc,neg_add_cancel,add_zero,abs_sub_comm] at hx; exact hx

include hw in
set_option maxHeartbeats 700000 in
lemma guard_varied (hF:varied F b): varied ((guardK M n m p) *ᵥ F) ((stone P (A.clock.J (m+1)))*b/(((A.S.block m)).val:ℝ)^3) := guard_varied_eq M P hp (fun n m hn=> (hw.2 n m hn).2) n m p hn F hb hF
omit hb in
lemma exact_curl : d 1 (A.S.side (m+1) p) * plane M n m p = ((M.H n (m+1)).dual_diag.acts (A.S.side (m+1) p))*(guardK M n m p)*(M.H n m).diagonal.acts (A.S.side m p)*d 1 (A.S.side m p):= by
   rw [Matrix.mul_assoc, Matrix.mul_assoc ((M.H n (m+1)).dual_diag.acts (A.S.side (m+1) p)), ← Matrix.mul_assoc (guardK M n m p),guardK,plane, (show installed (A.clock.op m p).ratio (M.towers n m).T * (M.H n m).diagonal.acts (A.S.side m p) * d 1 (A.S.side m p) = _ from (hp.crossings n m p hn).stays),← Matrix.mul_assoc,← Matrix.mul_assoc, mul_eq_one_comm.mp (hp.all n (m+1) hn (A.S.side (m+1) p)|>.diagonalInv),Matrix.one_mul]

omit hn in
lemma diagonal_bound (N p i) (hi:i≤N) (R : Row (TypeFace 2) (TypeFace 2)) (hR : R∈ ({(M.H N i).diagonal,(M.H N i).dual_diag}:Finset _)) {F:Co (A.S.side i p) (TypeFace 2)→ℝ} (hf:Bounded F b):
 Bounded (R.acts (A.S.side i p) *ᵥ F) (stone P (A.clock.J i)*b) := by
 let j:=A.clock.J i
 have hh:= hp.rows N i hi
 have ht : R.strip (P.α j) (P.Ω j):=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl|rfl <;> [exact hh.1; exact hh.2.2.2.2]
 have ht' := apply_bound R F hb hf (P.alpha_pos j).le ht
 exact fun x=> (ht' x).trans (by rw [←mul_one (Fintype.card (TypeFace 2):ℝ)]; exact stone_charge P _ shape_two (by positivity) hb ⟨zero_le_one,le_max_left ..⟩)

set_option maxHeartbeats 500000 in
lemma curl_bills (x:Body 1 (A.S.side m p)→ℝ) (hx : Bounded (d 1 (A.S.side m p) *ᵥ x) b): Bounded (d 1 (A.S.side (m+1) p) *ᵥ (plane M n m p *ᵥ x)) (grip P A m*b/((A.S.block m)).val^2):= by
   let i:=A.clock.J m; let j:=A.clock.J (m+1)
   let b':= stone P i*b; let b'':= stone P j*b'/((A.S.block m)).val^2
   have h0:=stone_one P; have hb' : 0≤b' := mul_nonneg (zero_le_one.trans <| h0 i) hb; have hb'' : 0≤b'':=by unfold b''; have hh:=h0 j; positivity
   intro y
   rw [mulVec_mulVec, exact_curl M P hp n m p hn, ←mulVec_mulVec,←mulVec_mulVec,← mulVec_mulVec]
   apply ((diagonal_bound M P hp hb'' n p (m+1) hn _ (by simp) ((guard_bound M P hp n m p hn _ hb' (diagonal_bound M P hp hb n p m hn.le _ (by simp) hx)))) y).trans_eq
   unfold grip; ring
omit hn in
lemma diagonal_varied (N p i) (hi:i≤N) (R : Row (TypeFace 2) (TypeFace 2)) (hR : R∈ ({(M.H N i).diagonal,(M.H N i).dual_diag}:Finset _)) {F:Co (A.S.side i p) (TypeFace 2)→ℝ} (hf:varied F b):
 varied (R.acts (A.S.side i p) *ᵥ F) (stone P (A.clock.J i)*b) := by
 let j:=A.clock.J i
 have hh:= hp.rows N i hi
 have ht : R.strip (P.α j) (P.Ω j):=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl|rfl <;> [exact hh.1; exact hh.2.2.2.2]
 have ht' := row_varied R F hb hf (P.alpha_pos j).le ht
 exact fun x a s=> (ht' x a s).trans (by rw [←mul_one (Fintype.card (TypeFace 2):ℝ)]; exact stone_charge P _ shape_two (by positivity) hb ⟨zero_le_one,le_max_left ..⟩)

set_option maxHeartbeats 500000 in
include heq in
lemma curl_varied_eq (x:Body 1 (A.S.side m p)→ℝ) (hx : varied (d 1 (A.S.side m p) *ᵥ x) b): varied (d 1 (A.S.side (m+1) p) *ᵥ (plane M n m p *ᵥ x)) (grip P A m*b/((A.S.block m)).val^3):= by
   let i:=A.clock.J m; let j:=A.clock.J (m+1)
   let b':= stone P i*b; let b'':= stone P j*b'/((A.S.block m)).val^3
   have h0:=stone_one P; have hb' : 0≤b' := mul_nonneg (zero_le_one.trans <| h0 i) hb; have hb'' : 0≤b'':=by unfold b''; have hh:=h0 j; positivity
   intro y a s
   rw [mulVec_mulVec, exact_curl M P hp n m p hn, ←mulVec_mulVec,←mulVec_mulVec,← mulVec_mulVec]
   apply ((diagonal_varied M P hp hb'' n p (m+1) hn _ (by simp) ((guard_varied_eq M P hp heq n m p hn _ hb' (diagonal_varied M P hp hb n p m hn.le _ (by simp) hx)))) y a s).trans_eq
   unfold grip; ring

set_option maxHeartbeats 500000 in
include hw in
lemma curl_varied (x:Body 1 (A.S.side m p)→ℝ) (hx : varied (d 1 (A.S.side m p) *ᵥ x) b): varied (d 1 (A.S.side (m+1) p) *ᵥ (plane M n m p *ᵥ x)) (grip P A m*b/((A.S.block m)).val^3):=
 curl_varied_eq M P hp (fun n m hn=> (hw.2 n m hn).2) n m p hn hb x hx
end step
end YM.Extension.UV.Linear
