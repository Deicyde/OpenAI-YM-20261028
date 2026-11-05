import YM.RG08.Sideshow.Kit
/-! # Leading matrix price and construction of the actual formal root iteration at one height.
 no uniformity from just this: doesn't communicate coefficients > listed horizon.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sideshow
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Room Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Necks
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries Matrix
variable {G:Gauge}{n D d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "E"=> Ed G Cover
variable (X:Labels.Frame G d)
local notation "I₀"=>Accent X
local notation "M₀"=>Playbook X
local notation "S₀"=>Bouquet X

def adj (Q:Crew G P K)(S:S₀):M₀:=evacuate (deposit X Q S) (fun i=>(P.L.val:ℝ)^(d-gamut i))
def sing (Q:Crew G P K)(S:S₀):S₀:=Atrium.shuffle (adj X Q S) (play Q S)
def Clean (S:S₀):Prop:=Atrium.ask S=1
lemma clean_value (S:S₀)(h:Clean X S)(i j:I₀)(e:ℕ):Trill.project X (S i) e j=if i=j∧e=0 then 1 else 0:=by
 have hh:=congrArg (fun (p:M₀)=>tap e (p j i)) (show Atrium.ask S=1 from h)
 change tap e (ballot _ _)=_ at hh;rw [ballot_value,Matrix.one_apply] at hh
 by_cases hi:i=j;subst j; simpa [tap,PowerSeries.coeff_one] using hh
 simpa [tap,PowerSeries.coeff_one,hi,Ne.symm hi] using hh
lemma clean_criterion (S:S₀)(h:Clean X S)(T:S₀)(he:Clean X T)(i:I₀)(e:ℕ):
 (∀ y:I₀,|project X (S i) e y| ≤ 1∧project X (S i) e y=project X (T i) e y)∧ ∀ z:I₀,gamut z<gamut i → project X (S i) e z=0:=by
 simp only [clean_value X S h,clean_value X T he,and_true];constructor
 · intro i;split_ifs <;> norm_num
 intro t H;rw [if_neg (mt And.left (by intro h;exact (not_lt_of_ge (le_of_eq (by rw [h]))) H))]
lemma cast_vote (Q:Crew G P K)(S:S₀)(e:ℕ)(i j:I₀):dusk e (deposit X Q S) j i=project X (Q.land d (octave i) (S i)) e j:= ballot_value ..
lemma gauge_scale (P:Side)(i:I₀) :1≤ (P.val:ℝ)^(d-gamut i):=one_le_pow₀ (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr P.pos.ne'))
-- C pre payable once. leading relationship for inverse before solving unmarked trajectory.
structure Monogram (P:Side)(C:ℝ)(M:M₀):Prop where
 funded:Arrow Atrium.street (fun i=>(P.val:ℝ)^(d-gamut i)) (ink M)
 pace:∀ i j:I₀,octave i=octave j→ |ink M i j|≤ C*(P.val:ℝ)^(d-gamut j)

lemma oriented (Q:Crew G P K)(S:S₀)(hc:Cloth (deposit X Q S))
 (h:∀ i u:I₀, octave u=octave i→ |ink (deposit X Q S) u i|≤ C*(P.L.val:ℝ)^(d-gamut i) ∧ (gamut u ≤ gamut i→ink (deposit X Q S) u i= if i=u then (P.L.val:ℝ)^(d-gamut u) else 0)):
 Monogram X P.L C (deposit X Q S):=by
 constructor
 · refine ⟨?_,fun i=>by simpa using (h i i rfl).2 le_rfl,fun i=>zero_lt_one.trans_le (gauge_scale X _ i)⟩
   intro i j he
   have hg:octave i ≤ octave j:=le_of_not_gt fun h=>he (by
      apply hc i j 0; omega)
   by_cases hi:i=j;exact .inl hi
   apply Or.inr
   change octave i < octave j ∨ octave i=octave j∧gamut j<gamut i
   rcases lt_or_eq_of_le hg with h'|h';exact .inl h'
   refine .inr ⟨h',lt_of_not_ge fun hz=>he ?_⟩;rw [(h _ _ h').2 hz,if_neg (Ne.symm hi)]
 intro i j hu;exact (h j i hu).1

lemma awake (D k j t:ℕ)(H:Hol G)(K:KernelChoices)(σ η τ μ V:ℝ)(h:Font d D k j t σ τ η μ V):∃ C:ℝ,1≤C ∧ ∀ {W δ:ℝ}{P:Patch}{Q R:Crew G P K}{S S':Bouquet X},Race σ τ η μ V W δ D d k (d+k) j t Q R→0<δ→Threads D S→Threads D S'→Deck X D k h.fine S→Deck X D k h.fine S'→Clean X S→Clean X S'→
 Monogram X P.L C (deposit X Q S)∧ Monogram X P.L C (deposit X R S'):=by
 choose A J hA hJ hz using fun i:I₀=>DocketBill X D (octave i) 0 (octave i) j t (d+k) H K σ η τ μ V (h.hired _ 0 _ (octave_le i) (by omega) (by omega)) (Nat.le_trans (octave_le i) (by omega)) (by omega)
 -- w=1 if J already? accepts W
 let C:=1+∑ i,A i;have hl(i):0 ≤ A i:=zero_le_one.trans (hA i);have hC:1 ≤ C:=le_add_of_nonneg_right (sum_nonneg fun i _=>hl _);have hW(i):A i≤C:=(single_le_sum (s:=univ) (f:=A) (fun i _=>hl i) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
 refine ⟨C,hC,fun {W δ P Q R S S'} hY hδ hs hs' hF hF' ha ha'=>?_⟩
 have he(i u:I₀)(hy:octave u=octave i):
 let g:ℝ:=P.L.val; let k:=d-gamut i
 let F:=ink (deposit X Q S) u i;let F':=ink (deposit X R S') u i
 ; (|F|≤C*g^k ∧ (gamut u ≤gamut i→ F=if i=u then g^(d-gamut u) else 0))∧ (|F'| ≤ C*g^k ∧ (gamut u≤gamut i → F'=if i=u then g^(d-gamut u) else 0)):=by
  intro g ka F F'
  obtain ⟨B,hB⟩:=deckAll X hF hF' hs hs' hδ i 0 (by omega)
  let n:=octave i;have ht:=hB n (by simp [n])
  obtain ⟨h1,h2⟩:=clean_criterion X S ha S' ha' i 0
  have hv (b r:ℕ)(hr:r≤n+b)(he:b<0∨b=0∧n<r) : Dyad (stance (Loc G 1)) D h.fine 0 δ (S i b r) (S' i b r):= False.elim (by omega)
  have h' := (hz i W hY.aps.tooth.base).2 (Q:=Q) (R:=R) (δ:=δ) (S:=S i) (S':=S' i) ⟨hY.aps.prices (by omega) le_rfl,hY.sold,hY.sold'⟩ (hs i) (hs' i) 0 B B B (B*δ) 1 le_rfl ht.price ht.price ht.price (mul_nonneg ht.price ht.rate) zero_le_one hv (fun r hr=>⟨(hB r hr).near,(hB r hr).far⟩) ht ht.near ht.far ht.switch (fun i _=>h1 i) _ (gamut_le i) (.inr ⟨rfl,fun i _=> h2 i⟩)
  have hx:=h'.booth;dsimp only at hx
  obtain ⟨hk1,hk2,-,hx⟩:=hx u (le_of_eq hy.symm); rw [mul_zero,add_zero,mul_one] at hk1 hk2
  unfold F F' ink; rw [cast_vote,cast_vote];refine ⟨⟨hk1.trans (mul_le_mul_of_nonneg_right (hW _) (by positivity)),?_⟩,hk2.trans (mul_le_mul_of_nonneg_right (hW _) (by positivity)),?_⟩
  · intro hu;rw [(hx rfl rfl hy hu).1,clean_value X S ha]; by_cases hq:i=u <;> simp [hq]; rfl
  intro hu;rw [(hx rfl rfl hy hu).2,clean_value X S' ha']; by_cases hq:i=u <;> simp [hq]; rfl
 exact ⟨oriented X Q S (overjoy X Q S hs).2 (fun i u hy=>(he i u hy).1),oriented X R S' (overjoy X R S' hs').2 (fun i u hy=>(he i u hy).2)⟩
end YM.RG08.Sideshow
