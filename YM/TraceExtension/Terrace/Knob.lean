import YM.TraceExtension.Terrace.Knell
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
section active
variable {G:Gauge}(F:Frame G 5)
abbrev night (v:F.Coeff):Prop:= F.act archV.ortho v= -v
lemma nights {v:F.Coeff}(h:night F v): F.core v=v :=by
    rw [drop,show v 0=0 from ?_]; simp
    have he:= congr_fun h 0; rw [sign_rows,F.zero_degree] at he; change _= -v 0 at he; norm_num at he; linear_combination he/2
abbrev Cgrade {d:ℕ}(F:Frame G d)(v:F.Coeff):Prop:= ∀ i:F.Index, i≠0 → v i≠0 → (F.grades i).1=d
lemma night_grade {v:F.Coeff} (h:night F v)(hG:G.Simple): Cgrade F v:=by
    intro i hi hj; have he := nbase F (Nat.le_refl _) i hi hG; have ht:= congr_fun h i; rw[sign_rows] at ht; change _=-v i at ht; by_cases hz:(F.grades i).1=5; exact hz; rw[show (F.grades i).1=4 from by omega] at ht; exfalso; apply hj; linear_combination ht/2
lemma even_grade(F:Frame G 4)(h:G.Simple)(v:F.Coeff): Cgrade F v:=by
   intro i hi hv; exact le_antisymm (F.bound i) (nbase F (by decide) i hi h|>.1)
lemma core_scale {d:ℕ}(T:Frame G d) {v:T.Coeff}(hG:G.Simple)(hd:d≤5)(u:ℝ)(L:Side)(h:Cgrade T v) : T.core (T.scaled u (vowel T L v))=(u^ (2:ℕ):ℝ) • T.core v:=by
    ext1 i; by_cases hi:i=0
    · subst i; change (update (T.scaled u (vowel T L v)) 0 0 0)= (u^2:ℝ) • (update v 0 0 0:ℂ);simp
    change (update (T.scaled u (vowel T L v)) 0 0 i)=(u^2:ℝ) • (update v 0 0 i:ℂ); rw[update_of_ne hi,update_of_ne hi,Frame.scaled_apply]; unfold vowel; by_cases hv:v i=0; simp[hv]; rw [h i hi hv, (nbase T hd i hi hG).2.2];simp[Complex.real_smul]
lemma count_smul {d:ℕ}(T:Frame G d) (c:ℝ)(v:T.Coeff): T.coeffSize (c • v)=‖c‖*T.coeffSize v:=by unfold Frame.coeffSize; simp only [Pi.smul_apply,norm_smul,Finset.mul_sum]
end active
variable {G:Gauge}(C:Family G) {d m N k p:ℕ}
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "Y"=> C.path.levels
def gearK {G:Gauge}(A:Levels G)(i:ℕ):=4*gear A i
def spine(d i N p:ℕ) (v:C.label d):= (((C.path.levels.budget i).threshold^ (2:ℕ))⁻¹:ℝ) • ((C.labels.level d).core (Cturn C d i N p v))
variable {W:Worth}(hq:Sceptre C W)
include hq
lemma readStep (h:C.ref d ≤ m)(hG:G.Simple)(hd:d≤5):∀ᶠ p in atTop,∀ N:ℕ,m < N → ∀ v:C.label d,Cgrade (C.labels.level d) (Cturn C d (m+1) N p v) →
       (F).coeffSize (spine C d m N p v-spine C d (m+1) N p v) ≤ gearK Y m * (F).coeffSize (spine C d (m+1) N p v):=by
    filter_upwards [hq.step d m hd h] with p hp N hN v hK
    obtain ⟨hv,hw⟩:= hp N hN v; let i:=m+1; let a:=((Y).budget m).threshold; let b:= ((Y).budget i).threshold; have ha:0<a:= ((Y).budget _).threshold_pos; have hb:0<b:= ((Y).budget _).threshold_pos
    let V:= spine C d m N p v; let V':=spine C d i N p v; let u:= Cturn C d i N p v; let w:= Cturn C d m N p v; let L:= C.S.block m
    let X:= (F).scaled (a/b) (vowel F L u);
    have ht : V'= (a^ (2:ℕ))⁻¹ • (F).core X:=by
        unfold X; rw [core_scale F hG hd _ _ hK,smul_smul, show (a^2)⁻¹*((a/b)^ (2:ℕ))=(b^2)⁻¹ from by field_simp]; rfl
    change (F).coeffSize (V-V') ≤ _* (F).coeffSize V'; nth_rw 1 [ht]; unfold V spine; change (F).coeffSize ((a^ (2:ℕ))⁻¹ • (F).core w-_) ≤ _; rw[← smul_sub,← map_sub,count_smul,Real.norm_of_nonneg (by positivity:0 ≤ (a^ (2:ℕ))⁻¹)];
    apply le_trans (mul_le_mul_of_nonneg_left (Work.G08.size_core F _ |>.trans hw) (by positivity)); change (a^2)⁻¹*(gear Y m * _ ) ≤ 4*_* (F).coeffSize ((b^ (2:ℕ))⁻¹ • (F).core u); rw[count_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (b^ (2:ℕ))⁻¹)]
    have he:(a^2)⁻¹ ≤ 4*(b^2)⁻¹:=by
       have hb:= (div_le_iff₀ ha).mp (show b/a≤2 from hv); field_simp; nlinarith only [hb, ‹0 < b›, ha, mul_le_mul_of_nonneg_left hb ‹0 < b›.le,mul_le_mul_of_nonneg_left hb ha.le]
    have hh := mul_le_mul_of_nonneg_left he (mul_nonneg (gear_pos Y m|>.le) (Work.G08.size_nonneg F ((F).core u)))
    change (a^2)⁻¹*(gear (Y) m * (F).coeffSize ((F).core u)) ≤ _; linarith only [hh]
omit hq
variable (H:C.Makes) {u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r D)
include H hr
lemma night_space (hk:C.ref 5 ≤ k)(h:k≤N)(v:C.label 5)(hv:night _ v): night (C.labels.level 5) (Cturn C 5 k N p v):=by
    unfold night; rw [← (guarded C H hr hk h v archV).2,hv]; exact ((nib_linear C H hk h).mk' _).map_neg v
end YM.Trace.Terrace
