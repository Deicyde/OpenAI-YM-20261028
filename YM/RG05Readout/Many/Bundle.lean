import YM.RG05Readout.Many.Stage
/-!
# Actual advance with ALL children of permuted preimage fibers

Coordinates P are prepared representatives of centered one-mark moves on Spine,
advancing up to real budget. Not dense K recodings. `License` may already
forbid sibling interactions; output is exact whole density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {n m p N:ℕ}{V W : Type}[DecidableEq V] [Fintype V][DecidableEq W][Fintype W] {R:Census V}{B:Census W}{a b c d t y z β:ℝ}
set_option quotPrecheck false
local notation "X"=> C.path
local notation "R₀"=> C.path.rep N p m
local notation "R₁"=> C.path.rep N p (m+1)
local notation "Ξ"=> C.path.levels.budget m
local notation "ξ"=> C.side (m+1) p
local notation "π"=> C.side m p
local notation "K"=> C.path.levels.clock.op m p
local notation "ψ"=> (K).ratio
local notation "L"=> C.S.block m
local notation "O"=> Address.Bud C p m
variable {o:W→Site (C.side m p)}{ν:V≃W×Address.Bud C p m}{x:V→Site (C.side (m+1) p)}{δ:W→Motion}
local notation "λ₀"=> Prod.fst ∘ ν
-- require raw census hLicense
variable {P: V→Three G (C.side (m+1) p)} {A:Config G (C.side (m+1) p)→Poly R} {s:W→ℕ}{Θ:W→Body}{w: V→ℝ} {r:ℕ→ℕ}{j:W→ℝ}{B₁:W→ℝ}
variable (h:C.Makes)
local notation "φ"=> fun i=> (((L).val):ℂ)^s (λ₀ i) -- ℂ

def budwgt (C:Family G)(p m k:ℕ):ℂ:= (↑((C.S.block m).val):ℂ)^k*(Fintype.card (Address.Bud C p m):ℂ)⁻¹ -- engineering scaled input m
variable {T: W→Tape G (C.side (m+1) p)} {S:W→Tape G (C.side m p)}
lemma bud_price (i:ℕ):‖budwgt C p m i‖≤ ((C.S.block m).val:ℝ)^i:=by
    unfold budwgt; rw [norm_mul,norm_pow,Complex.norm_natCast,norm_inv,Complex.norm_natCast]; apply mul_le_of_le_one_right (by positivity); apply inv_le_one_of_one_le₀; exact_mod_cast Fintype.card_pos
omit [DecidableEq V] in
lemma ave_merge (η:W→ Address.Bud C p m→Three G (C.side m p)):
    combine (λ₀) (fun i=>budwgt C p m (s (λ₀ i))) (fun i:V=>( (φ) i :ℂ)⁻¹ • (η (λ₀ i) (ν i).2))=fun j=>Address.average (η j):=by
    funext k; unfold combine; rw [← Equiv.sum_comp ν.symm]; dsimp only [Function.comp_apply]; simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single k,Address.average,Finset.smul_sum]; rotate_left
    · intro i _ hi; simp [hi] -- Fintype Ω
    · simp
    apply sum_congr rfl; intro a _; rw [if_pos rfl, smul_smul]; unfold budwgt; congr 1; have hv : ((L).val:ℂ) ≠ 0:=Nat.cast_ne_zero.mpr (L).property.ne'
    field_simp

omit [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] in
lemma parentExact (hX:∀ i:V,x i=affine (δ (λ₀ i)).1 ((ψ).embed (o (λ₀ i))) (Address.child C p m (ν i).2)) : (ψ).parent ∘ x=o ∘ λ₀:=by funext i; change (ψ).parent (x _)=_; rw [hX,Local.parent_affine _ (C.S.block_odd _),Address.Bud.personal]; simp [affine]
local notation "l₀"=> ((C.S.block m).val:ℕ)
set_option quotPrecheck false
local notation "shuttle" => fun i:O=> Native.pull (Address.displacement C p m i) (((C.S.block m).val:ℝ)⁻¹) -- operator cannot
section
variable {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} (hc:Coursework C.path r D a b c) (μ:∀ i,(C.path.rep N p m).activities.Moves (δ i).1 (o i))
variable {z:V→ℝ}{Z:W→ℝ}
include h hc
set_option maxHeartbeats 900000 in
lemma advance (hm:m<N) (H:∀ i:W,Train D (keys0 h hm) (d:=s i) (T i) (S i) (j i))
    (hx: MenuBoard (R₁) P A x w d 1)(hp:(C.path.levels.budget (m+1)).supportExponent-4≤d)(ho:Occupancy ((ψ).parent ∘ x) (r m)) (ho':Occupancy x (r m))
    (hf:∀ i:V,x i=affine (δ (λ₀ i)).1 ((ψ).embed (o (λ₀ i))) (Address.child C p m (ν i).2)) (hg:License B R λ₀)
    (hb:∀ i:V,let v:=(λ₀ i); Signpost (R₁) (δ v) (x i) ((T v) ((shuttle (ν i).2) (Θ v))) (P i))
    (ht:∀ i, Cap (s i+2) (Θ i) (B₁ i)) (hw:∀ i,0 < w i)(hy:∀ i,0<z i)(hz:Repegs (o ∘ (λ₀)) ((Ξ).B) (fun i=> a*w i) z (1/2) 1 R)
    (hℓ:∀ i:V,2*w i*(j (λ₀ i)*B₁ (λ₀ i)) ≤ 1) (hZ:∀ i,0< Z i) (hF:∀ i:V, Z (λ₀ i)* (((C.S.block m).val):ℝ)^(s (λ₀ i)) ≤ z i):
    MenuBoard (R₀) (fun i=> spin (δ i) (μ i) ((S i) (Θ i))) (fun U=>feed (fun i:V=>budwgt C p m (s (λ₀ i))) hg ((K).push (R₁).beta A U)) o Z ((Ξ).supportExponent) 1:=by
    have h'(i):∃ f:O→Tape G (C.side m p),(∀ k,Travel C N m p (s i) (Address.child C p m k) D ((Address.orient (keys0 h hm) (T i) k).comp (shuttle k)) (f k) (j i)) ∧ S i=Address.average f:=by obtain ⟨f,h,h'⟩:= H i; exact ⟨_,h,h'⟩
    choose f hA hq using h'; let χ := (λ₀); let Y (i:W) (a:O):= View.spin (δ i) (μ i) ((f i a) (Θ i)); let I i:= Y (χ i) (ν i).2
    let k(i:V):ℂ:= (φ) i; let V' i:= j (χ i)*B₁ (χ i)
    have hi(i:V): Ride (K) (x i) ((ψ).parent (x i)) D (k i) (P i) (I i) (V' i):=by
       let v:=χ i; let A₁ := (ν i).2; let X₁:=T v (shuttle A₁ (Θ v)); have he:= hA v A₁ (Θ v) _ (ht v)
       let θ':=((Address.orient (keys0 h hm) (T v) A₁).comp (shuttle A₁)) (Θ v)
       have hV:Signpost (R₁) (δ v) (x i) X₁ (P i):=hb i; rw [hf] at hV; have hu:=hc.publishes
       have hx':Signpost (R₁) (δ v) ((ψ).embed (o v)) θ' (P i):= hV.at_child View.shift_at
       have hv' : (ψ).parent (x i)=o v:= congr_fun (parentExact hf) i
       have hκ : Motion.scalar (δ v) (k i)=k i:=by unfold Motion.scalar; split; simp [k]; rfl
       have hh : Ride (K) (x i) (affine (δ v).1 (o v) 0) D (k i) (P i) (I i) (V' i):=by
          apply (show x i= _ from hf i).symm ▸ (View.paid h hm hu.propagate hκ he (hx.fettled _) (View.signpost_use h hm.le _ (μ v) he.tomorrow) hx' (spin_at ..))
       rw [show affine _ _ _ = o v by simp [affine]] at hh; rw [hv']; exact hh
    have hf' := parentExact hf; let fL:=fun i:V=>budwgt C p m (s (χ i))
    have hP:= hc.send h.wilson hm hx hp (fun i:V=> show 1 ≤ ‖k i‖ from (by rw [show k i=(((C.S.block m).val:ℕ):ℂ)^_ from rfl,norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (by exact_mod_cast (C.S.block m).property))) hw hi ho' ho hℓ hy (hf'.symm ▸ hz)
    have hZ':= hP.blend fL hg (h.wilson.represents N p m hm.le).good hf' (fun i=> show Z (λ₀ i)*‖fL i‖ ≤ z i from (mul_le_mul_of_nonneg_left (bud_price _) ((hZ ..).le)).trans (hF i)) hy hZ
    have hQ : combine (λ₀) fL (fun i:V=> (k i)⁻¹ • I i)= fun i=> spin (δ i) (μ i) ((S i) (Θ i)):=by
       rw [ave_merge Y]; funext i; rw [hq]; unfold Address.average
       let r':=(Fintype.card O:ℂ)⁻¹; rw [LinearMap.smul_apply,LinearMap.sum_apply,spin_real,spin_sum]
       unfold Motion.scalar; split; simp; rfl
    rw [hQ] at hZ'; exact hZ'
end
end YM.RG05Readout.Many
