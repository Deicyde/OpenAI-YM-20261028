import YM.MergeProof.North.Anise
import YM.OPE.Grouping.Care
import YM.OPE.Grouping.Charge
import YM.OPE.Replicas.Arbor

/-!
# Grouped & elementary output analysis costs

Core grouping lemma (`materialize`), still before the March to the next level. Uses
*quantitative* budget of the remounted collection. Unit costs included. Analogous to
`grafted` (North/Anise); here we remember also the output Deck polynomials so we know
precisely which `Horn` condition to provide after repeated reaping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I O : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}{n:Side}{R:Rep G n}{t a x b: ℝ}{w:V→ℝ}{L:Fibers I V}
variable (S:Salt V I L G n)
variable {J:I→ℝ} {Z y c q d z:ℝ}
variable (s l:ℕ)(η T Z :ℝ)
set_option quotPrecheck false
local notation "y!"=> Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η a b
local notation "τ" => R.p.threshold
variable (k:ℕ) (hk:0 < k)
local notation "W₁"=>Salt.tow J (R.p.supportExponent+c) (η/k) l
namespace Salt
def debt (S:Salt V I L G n) (t:ℝ) (v:V) (U:Config G n) := (Mach (Bud V) 0+ ∑ i,S.mount t i U).part ((Bud V).fire v)
def income (R:Rep G n) (S:Salt V I L G n) : Config G n→Poly (Bud I) :=
    play R (Bud I) S.river (fun U=>Mach (Bud I) S.pepper+∑ i, S.air i U)
structure Birth (h:Config G n→Poly (Bud I))(u:V→ℕ→ Config G n→ℂ)(w:V→ℝ)(R:Rep G n)(Z:ℝ): Prop where
  foot i : Dominated (u i) ∧ Blade R (S.focus i) (S.debt R.p.threshold i) (profile R.activities (u i)) 0 (4*(Z/w i))
  costs i j U : (S.soil R.p.threshold j U).part ((Bud V).fire i)=profile R.activities (u i) j U
  meets : Carton S.focus (fun i U=>octave (S.mount R.p.threshold i U)) (fun i U=>octave (S.soil R.p.threshold i U)) R.p.threshold
  equal : (fun U=> Fibers.reap L (h U))=restore R (S.debt R.p.threshold) (fun i=> profile R.activities (u i)) (fun i U=>octave (S.mount R.p.threshold i U)) (fun i U=>octave (S.soil R.p.threshold i U))
  arc : Towed w id (fun i U=>octave (S.mount R.p.threshold i U)) R.p.B R.p.supportExponent Z
  pots : Towed w Prod.fst (fun i U=>octave (S.soil R.p.threshold i U)) R.p.B R.p.supportExponent Z
include hk
lemma materialize (A:Arsenal R)(h0:S.Breeze (τ))(hr:R.activities.Valid R.p z d)(he:∀ i U, (S.river i U).part (Bud I).quiet=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U)
    (hw:∀ i,0<J i)(hv:Occupancy S.grain s)(ht:0≤T)(hy:∀ i,J i*‖S.pepper i‖ ≤ T)(hm:0<R.p.B)(hX:0<η)(hY:η≤1)(hS:∀ i:I,coverNumber R.p.B ({S.focus (L.bunch i), S.grain i}:Support n)≤ l)(hc:0≤ c)
    (hF: Towed J id S.air R.p.B (R.p.supportExponent+c) a)(hK:Towed J Prod.fst S.river R.p.B (R.p.supportExponent+c) b)
    (hP:∀ i : V,(L.contents i).card ≤ k) (hit:∀ U,R.eval U≠0)(hu:∀ i,w i= ∏ j∈L.contents i,W₁ j)(hJ: ((R.p.B + R.p.B + 1 : ℕ):ℝ)^4*(y!) ≤ c)(hξ: Real.exp (y!)-1≤ Z) :
    ∃ u:V→ℕ→ Config G n→ℂ, Birth S (income R S) u w R Z :=by
    let D:=S.vessel τ
    let V₀ i U:=S.mount τ i U; let V₁ i U:=S.soil τ i U
    have hv':D.Rated W₁ R.p.B (R.p.supportExponent+c) (y!) := S.rate J τ (R.p.supportExponent+c) T η s _ l hw hv hy hm hX hY hS k hk hP a b ht hF hK (add_nonneg R.p.exponent_pos.le hc)
    have hM:= S.turn τ h0; have hE := S.wet _ h0; have hW (i:I): 0<W₁ i := Salt.towP _ _ _ _ hw (by positivity) _
    obtain ⟨hb,hh⟩:= D.carries τ hE W₁ w R.p.supportExponent c (y!) R.p.B hv' R.p.exponent_pos.le hW hu hJ
    have hWp i:0 < w i:=by rw [hu]; exact prod_pos fun _ _=> hW _
    have ht:=hb.shrink le_rfl hξ hWp; have hT:=hh.shrink le_rfl hξ hWp
    let y' U := Mach (Bud V) 0+ ∑ i,V₀ i U; let gy(v:V)(U):=(y' U).part ((Bud V).fire v)
    obtain ⟨j,hR,hS',hC,hJ'⟩:= Ribbons.plume (F:=V₀) (K:=V₁) A hr (fun i=> D.clearBurn τ hE hM i) (fun i=>D.cloudy τ hE hM i) ht hT hWp (fun i U=>(S.taxed τ U h0 i).trans (he ..)) hit 0
    refine ⟨j,fun i=>⟨(hR i).1,(by rw [show 4*(Z/w i)=2*(Z/w i)+2*(Z/w i) from (by ring)]; exact (hR i).2)⟩, hS', hC, Eq.trans ?_ hJ',Towed.sift ht,Towed.sift hT⟩
    funext U; unfold income play; dsimp only; rw [map_smul,Ribbons.blank_mach,zero_add,S.yields _ U h0]
omit hk
variable {S Z}
namespace Birth
variable {F:Config G n→ Poly (Bud I)}{u:V→ℕ→ Config G n→ℂ}(h: S.Birth F u w R Z)
include h
lemma served : Served R (S.debt τ) (fun i=> profile R.activities (u i)) (fun U=> Fibers.reap L (F U)) S.focus w R.p.supportExponent Z := ⟨_,_,h.meets,h.arc,h.pots,h.equal⟩
variable {x:Site n}{m:Motion}{a₀:Equiv.Perm I} {b₀ : Equiv.Perm V}{C G':Set V}
  (H : CopyFamily S R.p.threshold m x C G' a₀ b₀)
include H
set_option maxHeartbeats 800000 in
lemma travels {j:V} (hi:j∈C) : S.debt τ (b₀ j)=stepUp m x (S.debt τ j) ∧
    profile R.activities (u (b₀ j))=floatUp m x (profile R.activities (u j)):=by
    have ht : (((Bud V).fire j).val:Set V) ⊆ C:= by simpa [Census.fire] using hi
    have hp (U:Config G n):= H.twines U ((Bud V).fire j) ht
    constructor
    · funext U; unfold debt stepUp; simp_rw [Ribbons.blank_mach,zero_add,Poly.part_sum]; rw [Float.summer,← Equiv.sum_comp (sky m x)]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Fibers.fires b₀ j]; exact (hp U).1 i
    funext i U; unfold floatUp stepUp; obtain ⟨i,hp'⟩:= (puff m x).surjective i; rw [← hp',Equiv.symm_apply_apply, ← h.costs,← h.costs,Fibers.fires b₀ j]; exact (hp _).2 i
end Birth
end Salt
end YM.MergeProof.Ribbons.Fibers
#print axioms YM.MergeProof.Ribbons.Fibers.Salt.Birth.travels

