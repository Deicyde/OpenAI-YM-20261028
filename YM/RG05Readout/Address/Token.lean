import YM.RG05Readout.Address.Warp
/-!
# Trace extension in test argument from finer to parent

Compare existing price via `Ride.matchPay`. One evaluation bound uniform
in the plant. For additivity no universal bound on extension of log beyond
this lift is assumed. Finite root alternative census afterwards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}{C:Family G}{N m p d:ℕ}
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level
local notation "Y"=> C.params
local notation "S"=> C.localSection
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable (C N m p d) (b:Site (C.side (m+1) p)) (D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
-- no adjacency restriction in this definition, instantiations include root geometry

def Travel (P:Tape G (C.side (m+1) p))(Q:Tape G (C.side m p))(x:ℝ):Prop :=
   ∀ φ:Body,∀ t:ℝ,Cap (d+2) φ t → Ride Z b 0 D v (P φ) (Q φ) (x*t)

section
variable {C N m p d D b}{P F':Tape G (C.side (m+1) p)}{U Q:Tape G (C.side m p)}{x a w:ℝ}
lemma Travel.extend (h:Travel C N m p d b D P Q x)(he:x≤a):Travel C N m p d b D P Q a:=by intro φ t hp; exact (h φ t hp).cost (mul_le_mul_of_nonneg_right he hp.nonneg)
lemma Travel.add (h:Travel C N m p d b D P Q x)(h':Travel C N m p d b D F' U a)(hz:C.Makes)(hm:m<N)(hp:SoundDoor Z D): Travel C N m p d b D (P+F') (Q+U) (x+a):=by
    intro φ t hc; rw [LinearMap.add_apply,LinearMap.add_apply,add_mul]; exact (h φ t hc).taller (h' φ t hc) hp (C.path.levels.transition_mass ..) (hz.wilson.represents _ _ _ hm).good (hz.wilson.represents N p m hm.le).good
lemma Travel.smul (h:Travel C N m p d b D P Q x) (z:ℂ): Travel C N m p d b D (z • P) (z • Q) (‖z‖*x):=by
    intro φ t hc; rw [LinearMap.smul_apply, LinearMap.smul_apply,mul_assoc]; have ht:=(h φ t hc).matchPay z z v (mul_comm ..); rw [max_self] at ht; exact ht
lemma Travel.vac (hx:0≤x) : Travel C N m p d b D 0 0 x:=by intro φ t h; exact Ride.cost (q:=0) (p:=0) Ride.vac (mul_nonneg hx h.nonneg)
lemma Travel.list {ι:Type*}{P:ι→Tape G (C.side (m+1) p)}{F':ι→Tape G (C.side m p)}{k:ι→ℝ} (I:Finset ι)(hz:C.Makes)(hm:m<N)(hp:SoundDoor Z D)(hh:∀ i∈ I,Travel C N m p d b D (P i) (F' i) (k i)):
    Travel C N m p d b D (∑ i∈I,P i) (∑ i∈I,F' i) (∑ i∈I,k i):=by
    induction I using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Travel.vac le_rfl
    | @insert i I hi ih=> simp_rw [Finset.sum_insert hi]; exact (hh i (Finset.mem_insert_self ..)).add (ih (fun i' hi'=>hh i' (Finset.mem_insert_of_mem hi'))) hz hm hp

-- old stamp evaluated with displacement variable of test. Future output stays at parent in the full order
lemma Travel.scaleTo (p':Three G (C.side (m+1) p)) (q':Three G (C.side m p)) (ζ:PulseC)(h:Priced d ζ w) (k:Letter d) (hu:Ride Z b 0 D (((L).val:ℂ)^(kept k)) p' q' x):
    Travel C N m p d b D ((↑(ℓ ^depth k):ℂ) • glyph ζ p') (glyph ζ q') (w*x):=by
     intro φ z hφ; simp only [LinearMap.smul_apply, glyph_apply]; rw [smul_smul]
     have ht:=hu.matchPay ((↑(ℓ ^depth k):ℂ)*(ζ φ)) (ζ φ) (v) ?_
     · refine ht.cost ?_
       have hy : ‖(↑(ℓ^depth k):ℂ) * ζ φ‖≤ ‖ζ φ‖:=by
          have hs:0<(((L).val):ℝ):= by positivity
          rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hs).le _)]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (inv_pos.mpr hs).le (by rw [inv_le_one₀ hs]; exact_mod_cast (L).property))
       rw [max_eq_right hy, mul_right_comm w]; exact mul_le_mul_of_nonneg_right (h _ _ hφ) hu.nonneg
     have hp: kept k + depth k=d:=Nat.sub_add_cancel (Nat.le_of_lt_succ k.1.isLt); rw [← mul_assoc]
     have he: v=(↑((L).val):ℂ)^(kept k)*(↑((L).val):ℂ)^(depth k):=by
        rw [← pow_add,hp]
     rw [he,mul_assoc ((↑((L).val):ℂ)^(kept k)),Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_natCast, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (show ((↑((L).val)):ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (L).property.ne')), mul_one, mul_comm]
lemma cappay(d:ℕ)(f:PulseC) (z:ℂ)(h:Priced d f x):Priced d (z • f) (‖z‖*x):=by
    intro φ t hc; rw [LinearMap.smul_apply,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h _ t hc) (norm_nonneg _)
end
end YM.RG05Readout.Address
