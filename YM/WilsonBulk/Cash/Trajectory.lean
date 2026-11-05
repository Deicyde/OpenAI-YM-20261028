import YM.WilsonBulk.Cash.Compass

/-!
# Reroot ordinary potential bound with all phases

Teles to plain public travel using A0. Does NOT buy affine-null rank0 nor rank projections.
Uses `careGrow=(n+1)` scale on input weights for WT footprint; account before issuing length!
Tracks L costs for gauge cancellation only with `toll*ηHeight`. This is chosen post-block.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {f c L : Side} {n k e : ℕ} {P : Patch} {K : KernelChoices}
variable {B Z T : Pace P.L G} {σ θ A C x y η M ε : ℝ}

abbrev Walls (V : Pace P.L G) (n : ℕ) (σ A : ℝ) := AuditLine (install V) (spotCost P.L σ) n A A
lemma wall_front {V U : Legs (Pace P.L G) (n+1)} {F : Text (Cloth G) (n+1)} {D : ℕ→Side} (d : Fin (n+1))
    (hp : GrowsHigh G B Z T K D) (he : Tendsto (fun i=> (D i).val) atTop atTop) (ht : U d=B) (hz : V d=Z) (hv : ∀ i≠d,V i= U i) (h : Public F) (hF : Regular F)
    (hB : ∀ i, Lighthouse (U i)) (hZ : Lighthouse Z) (hT : Lighthouse T) (hu : ∀ i, Walls (P:=P) (U i) (n+1) σ A)
    (hs : 0≤σ) (hw : σ/P.L.val≤θ) (hk : Walls (P:=P) T (n+1) σ A) (hx : Within (lawn (Cloth G)) θ x (diss backed F)) :
    Within (lawn (Cloth G)) σ (A*A^n*x) (tele (install ∘ V) F - tele (install ∘ U) F) := by
  let v:= Equiv.swap 0 d; have H: v 0=d := Equiv.swap_apply_left ..; let H':=crop (U ∘ v); have hh : Plaza H':= plaza fun j=> hB _
  have hX : ∀ j : Fin (n+1), Walls (P:=P) (hitch T H' j) (n+1) σ A:= fun j=> by cases j using Fin.cases with
    | zero => exact hk
    | succ i=> simp only [hitch_succ]; exact hu _
  let W := tele (install ∘ hitch T H') (diss backed F); have hW : Within (lawn (Cloth G)) σ (A*A^n*x) W:= fare_const (delta_shape hs hw) hX hx
  have hu' : B= (U ∘ v) 0:= by rw [Function.comp_apply,H,ht]
  have hv' : Z= (V ∘ v) 0:= by rw [Function.comp_apply,H,hz]
  have ht' : H'=crop (V ∘ v):= by ext1 j; change U (v j.succ)=V (v j.succ); exact Eq.symm (hv _ (H ▸ v.injective.ne (Fin.succ_ne_zero _)))
  have hw : escort v.symm (tele (install ∘ V) F-tele (install ∘ U) F)=W := by
    rw [escort_minus,show escort v.symm (tele (install ∘ V) F)=_ from (teleport_escort _ v F).symm,show escort v.symm (tele (install ∘ U) F)=_ from (teleport_escort _ v F).symm,hF v.symm,Function.comp_assoc,Function.comp_assoc, ← show hitch B H'=U ∘ v from hu' ▸ hitch_crop _, ← show hitch Z H'=V ∘ v from by rw [ht',hv',hitch_crop]]
    exact audit_polar (P:=P) _ h hp hh (ht ▸ hB _) hZ hT he -- remove explicit?
  rw [show _ - _ = escort v W from by rw [← hw, escort_escort, symm_trans_self]; rfl]; exact hW.reindex _

def turbulent (P : Patch) (σ θ x : ℝ) (G : Gauge) (n : ℕ) := receipt (Cloth G) (Cloth G) σ θ x (fitting n) n / (P.L.val:ℝ)
def strictWall (A : ℝ) (G : Gauge) (e n : ℕ) := ((n+1:ℕ):ℝ)*(A*(A^n)*knee G e n)
lemma strictWall_nn (hA : 0≤A) : 0≤strictWall A G e n := mul_nonneg (by positivity) (mul_nonneg (by positivity) (knee_nn ..))
lemma turbulent_nn (hp : 0≤θ) (h : 0≤ x) : 0 ≤ turbulent P σ θ x G n:= div_nonneg (Sheet.receipt_nonneg hp h) (by positivity)

lemma climbing (h : GrowsHigh (P:=P) G B Z T K (cascade 1)) {I : Library G} (hh : Whisper I) (hN : BodyNull I)
    (hB : Heights (L:=P.L) B (fitting n) η x) (hZ : Lighthouse Z) (hT : Lighthouse T)
    (hb : Walls (P:=P) B (n+1) σ A) (hz : Walls (P:=P) Z (n+1) σ A) (hL : Walls (P:=P) T (n+1) σ A)
    (hs : 0<σ) (hx : (n+1:ℕ)*σ≤η) (hp : 0< θ) (he : θ≤1) (ht : σ/P.L.val ≤ θ/2) (hq : pulseGrow (σ/P.L.val) n ≤ θ)
    (hV : Within (lawn (Cloth G)) θ M (I e (n+1)))
    (hr : ∀ i:ℕ,0 < i → i ≤ e → i ≤ n → Within (lawn (Cloth G)) θ y (I (e-i) (n-i+1))) :
    Within (lawn (Cloth G)) σ (turbulent P σ θ x G n * M + strictWall A G e n * y) (Sheet.travel (install Z) (I e (n+1))) := by
  let V:=I e (n+1); have hF : Regular V := hh.style.coherent _ _; have hx' := pulse_cost hh he hq (div_nonneg hs.le (by positivity)) hp.le hr; let D : ℝ:= A*A^n*(knee G e n*y)
  have hc : Lighthouse B:= by
    have he:= hB.2 [] (by simp); have hc:= hB.1; exact ⟨η, (mul_pos (by positivity) hs).trans_le hx,_, by positivity, he⟩
  -- telescope across arbitrary i in same output. Strict wall consumes e LESS never rank same terms
  let v (s : Finset (Fin (n+1))) (j : Fin (n+1)) := if j∈s then Z else B; let Y s := tele (install ∘ v s) V
  have hi (s) : Within (lawn (Cloth G)) σ ((s.card:ℝ)*D) (Y s-Y ∅) := by
    induction s using Finset.induction with
    | empty => rw [sub_self,card_empty]; simp only [Nat.cast_zero,zero_mul]; exact Within.zero le_rfl
    | insert a s H ih =>
       have hh' : Within (lawn (Cloth G)) σ D (Y (insert a s)-Y s) := wall_front (V:=v (insert a s)) (U:=v s) a h cascade_up (if_neg H) (if_pos (mem_insert_self ..)) (by intro j h; simp [v,h]) (hh.palm _ _) hF (fun i=>by unfold v; split <;> assumption) hZ hT (fun i=> by unfold v; split <;> assumption) hs.le le_rfl hL hx'
       have hv:= hh'.add ih; rw [sub_add_sub_cancel] at hv; refine hv.mono le_rfl (Eq.le ?_); rw [card_insert_of_notMem H]; push_cast; ring
  have hP : Within (lawn (Cloth G)) σ (turbulent P σ θ x G n*M) (Y ∅) := by
    have hO := pruned_price hp (hN e n) hF hV hs.le ht P.odd_side hB hx (by unfold fitting; omega); refine Eq.mp ?_ hO
    simp [Y,v,Sheet.travel,V,turbulent]; rfl
  have hv:= hi univ
  rw [card_univ,Fintype.card_fin] at hv
  have ht' := hv.add hP; rw [sub_add_cancel, add_comm _ (turbulent _ _ _ _ _ _* M)] at ht'; convert! ht' using 1
  · unfold strictWall D; ring
  · unfold Y v Sheet.travel; congr! 1; ext1 i; simp
end Parapet
end YM.WilsonBulk
