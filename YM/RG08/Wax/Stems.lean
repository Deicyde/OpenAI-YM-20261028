import YM.RG08.Wax.Ranks
/-! # Fine local estimation pipeline on finite mark count and arbitrary
 prescribed geometry carriers. Solved for the stated family.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores Finset Push.AbsoluteSums UVExt.Paths Town Work.F08
open scoped Topology BigOperators Real Classical
variable {I X:Type} [Fintype I] [DecidableEq I][Fintype X][DecidableEq X] {i j e E k n τ r t l D:ℕ}{v w B C R:ℝ}
variable {M:Row X X}{S:Canticle X}{A: Places I→ Mill I X D R}
def resp (I:Type)[Fintype I][DecidableEq I](t E:ℕ)(r B C:ℝ)(n:ℕ):ℝ:= match n with
    | 0=> B
    | n+1=> let b:= resp I t E ((parPort I t:ℝ)*r) B C n
            b+∑ T:Finset I,∑ i∈range (t+1),∑ j∈range (E+1), posSticks r b C i j n T
lemma port_pos (I:Type)[Fintype I](t:ℕ):0<(parPort I t:ℝ):=by unfold parPort; push_cast; positivity
lemma resp_z (I:Type)[Fintype I][DecidableEq I](n:ℕ) (hv:0<v)(hc:0≤C)(hb:0≤B):0 ≤ resp I t E v B C n:=by
    induction n generalizing v with
    | zero=> exact hb
    | succ n ih=>
      rw [resp]; have hB:= ih (mul_pos (port_pos I t) hv); exact add_nonneg hB (sum_nonneg (fun T _=> sum_nonneg fun j _=> sum_nonneg fun i _=> sticks_live _ _ _ _ _ _ _ hv hB hc))
def advanceFee (I:Type)[Fintype I](t:ℕ)(v:ℝ)(n:ℕ):= (parPort I t:ℝ)^n*v
lemma advance_v (I:Type)[Fintype I](hv:0≤v)(he:n ≤ i): advanceFee I t v n≤ advanceFee I t v i:= mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (show (1:ℝ) ≤ (parPort I t:ℝ) by norm_cast; unfold parPort; omega) he) hv
lemma orbit_sleep (R:ℝ)(hk:0≤R){A:Mill I X D R}(hp:Whole M) (hx:Gets S)(he : ∀ t i j,Tidy (A t i j))(F:A ∅=0) : orbitV none M S A ∅=0:= by
   funext i j k; apply tapUni; intro x
   rw [show sampleK ∅ x ∘ (orbitV none M S A ∅ i j k)=taps_at x (orbitV none M S A) ∅ i j k from rfl, orbit_e x hp hx he hk,pulse_void _ hp hx (access_nil _ F)]; ext; simp
variable {a:I→ℕ}{P:Head I}
lemma resp_price (hP:Crease P)(hp:0≤R)(ha:∀ i t,Fits (vanes a t) (A i t))(hq:∀ t,vanes a t+E≤τ) (hc:∀ i j e r,Tidy (A i j e r))(hx:∀ i,A i ∅=0)
    (hw:0<v)(hG:advanceFee I τ v n≤w)(hS:Gets S)(hC:0≤C)(hB:0≤B)(hM:M.strip w C)(hK:∀ i≤n,∀ j≤E,∀ k,Glow (Refrain M S none i j k) w C)
    (hV:∀ T i,i≤E →∀ r, Owns w T (fun p=> A p T i r) (B*P T)) :
      carnival P v (resp I τ E v B C n) (fun x=>orbitV none M S (A x)) n E := by
   have hj : v≤w:=(by simpa [advanceFee] using advance_v (i:=n) I hw.le (Nat.zero_le n) (t:=τ):v ≤ advanceFee I τ v n).trans hG
   have hv : Whole M:=⟨_,_,hw.trans_le hj,hM⟩
   induction n generalizing v with
   | zero=> rintro j hi i he t r; simp_rw [show j=0 by omega,orbit_z]; exact owns_mono (hV t i he r) hj le_rfl -- fix
   | succ n ih =>
      let z:=(parPort I τ:ℝ)*v; have hz:0<z:=mul_pos (port_pos ..) hw
      have hx':advanceFee I τ z n≤w:=(show advanceFee I τ z n= advanceFee I τ v (n+1) from by rw [advanceFee,advanceFee,pow_succ,mul_assoc]).trans_le hG
      have hw':z≤w:=(by simpa [advanceFee] using advance_v (i:=n) I hz.le (Nat.zero_le n) (t:=τ):z ≤ advanceFee I τ z n).trans hx'
      let V:= fun x=> orbitV none M S (A x)
      let b:= resp I τ E z B C n; let Z:=resp I τ E v B C (n+1)
      have hT : carnival P z b V n E:= ih hz hx' (fun i hi=>hK i (hi.trans (Nat.le_succ _))) hw'
      have hb:0≤b:=resp_z I n hz hC hB
      have ht T r i: 0≤posSticks (I:=I) v b C r i n T:=sticks_live _ _ _ _ _ _ _ hw hb hC
      have hi : b≤Z:= le_add_of_nonneg_right (sum_nonneg (fun (T:Finset I) _=> sum_nonneg (s:=range (τ+1)) fun r _=> sum_nonneg (s:=range (E+1)) fun i _=> ht T r i)) -- resp unfolds
      let S' (x:Places I)(t:Finset I)(i:ℕ):= if H:i≤n then V x t i else 0
      have he(t:Finset I)(x:Places I): V x t (n+1)= ((↑(n+1:ℕ)):ℝ)⁻¹ • blue none M S (S' x) t n := by unfold V; rw [orbitV]
      have hq':sleeps S':= fun x=>funext fun i=>by
        dsimp only [S']; split; rw [show V x ∅=0 from orbit_sleep R hp hv hS (hc x) (hx x)]
        rfl
      intro i hJ j hr T r
      by_cases hL:i≤ n; · exact owns_mono (hT i hL j hr T r) (port_w I τ hw.le) (mul_le_mul_of_nonneg_right hi (hP.pos T))
      have hX:=resp_z I (n+1) hw hC hB (E:=E) (t:=τ)
      change Owns v T (fun x=> V x T i j r) _
      by_cases hd:r≤τ
      · simp_rw [show i=n+1 by omega,he]
        apply owns_mono (owns_s (sticks_pass hP hw hp hq' ?_ hb hC (le_refl z) hd le_rfl hr (strip_mono hM hw' le_rfl) ?_ T) (↑(n+1:ℕ):ℝ)⁻¹) le_rfl ?_
        · intro i hi k hk T r
          simp_rw [S',dif_pos hi]; exact hT i hi k hk T r
        · intro i hi k hk t; exact glow_less (hK i (hi.trans (Nat.le_succ _)) k hk t) hw' le_rfl
        rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (hP.pos _)
        have hK : ‖(↑(n+1:ℕ):ℝ)⁻¹‖≤1:= by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]; apply inv_le_one_of_one_le₀; push_cast; linarith
        refine (mul_le_of_le_one_left (ht T r j) hK).trans ((single_le_sum (f:=fun k=>posSticks v b C r k n T) (fun i _=> ht T r i) (show j∈ range (E+1) from mem_range.mpr (by omega))).trans ?_)
        apply le_trans (single_le_sum (f:=fun r=> ∑ i∈range (E+1),posSticks v b C r i n T) (fun i _=> sum_nonneg fun j _=>ht T i j) (show r∈range (τ+1) from mem_range.mpr (by omega)))
        rw [resp]; exact (single_le_sum (f:=fun T=>∑ i∈range (τ+1),∑ j∈range (E+1),posSticks v b C i j n T) (fun T _=>sum_nonneg fun i _=> sum_nonneg fun j _=> ht T i j) (mem_univ T)).trans (le_add_of_nonneg_left hb)
      have he x : V x T i j r=0:= not_ne_iff.mp fun h=>by have hu:= (orbit_cap hv hS (hc x) hp (ha x) T i) j r h; have hh:=hq T; omega
      simp_rw [he]; exact owns_none _ _ (mul_nonneg hX (hP.pos _)) _ _ _

def Fest (w:ℝ)(K:ℕ)(B:ℝ)(a:Head I)(A:Places I → Mill I X D R):Prop:=∀ i≤K,∀ j t,Owns w t (fun x=>A x t i j) (B*a t)
-- export usable for **every successive F**, no variation-dependent constant for predecessor inputs.
lemma noon_fees (hP:Crease P)(hp:0≤R)(ha:∀ x t,Fits (vanes a t) (A x t))(hq:∀ t,vanes a t+E≤τ)(hc:∀ x t i j,Tidy (A x t i j))(hx:∀ i,A i ∅=0)
    (hw:0<v)(hG:advanceFee I τ v (windows τ E)≤w)(hS:Gets S)(hC:0≤C)(hB:0≤B)(hM:M.strip w C)(hK:∀ i≤windows τ E,∀ j≤E,∀ k,Glow (Refrain M S none i j k) w C)
    (hV:Fest w E B P A) : Fest v E ((↑(windows τ E+1:ℕ):ℝ)*resp I τ E v B C (windows τ E)) P (fun x=>noon M S a (A x)):= by
   intro i hi r t; let b:=windows (vanes a t) i; let c:=windows τ E; let Y:= resp I τ E v B C c
   have hh:carnival P v Y (fun x=>orbitV none M S (A x)) c E:=resp_price hP hp ha hq hc hx hw hG hS hC hB hM hK (fun T i hi r=> hV i hi r T)
   have hb : b≤ c:= by have ht:= hq t; unfold b c windows; omega
   refine owns_mono (owns_sum (U:=fun i' x=>orbitV none M S (A x) t i' i r) (range (b+1)) (fun j hj=> hh j (by have hv:=mem_range.mp hj; omega) _ hi _ _)) le_rfl ?_
   have hx':0≤Y:=resp_z I _ hw hC hB; rw [sum_const,card_range,nsmul_eq_mul,mul_assoc]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) (mul_nonneg hx' (hP.pos _))
end YM.RG08.Wax
