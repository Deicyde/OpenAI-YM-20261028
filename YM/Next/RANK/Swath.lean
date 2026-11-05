import YM.Analysis.Polydisc
import YM.Next.RANK.EntryWord


/-!
# Flagged price tests commute with moves on REAL records
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Thirst
open Function Filter RG Lattice Wilson Finset MeasureTheory Relation Corona
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} (s : Signed) (x : Site n)

def sends : Equiv.Perm (Site n):= s.actEquiv.toEquiv.trans (Equiv.addRight x)
def swath (P : Support n) := P.image (affine s x)
lemma stay (P : Support n) {i : Site n} : affine s x i∈ swath s x P ↔ i∈P := by
  constructor
  · intro hi; obtain ⟨c,hc,hp⟩:= mem_image.mp hi; rw [← (sends s x).injective hp]; exact hc
  exact fun hi=> mem_image_of_mem _ hi
lemma s_comp (r : Signed) (y z : Site n) : affine s x (affine r y z)=affine (s*r) (affine s x y) z := by simp [affine,Signed.act_mul,add_assoc]
lemma swath_comp (r : Signed) (y : Site n) (P : Support n) : swath s x (swath r y P)= swath (s*r) (affine s x y) P := by unfold swath; rw [Finset.image_image]; apply Finset.image_congr; exact fun i _=> s_comp ..
lemma swath_inv (P : Support n) : swath s⁻¹ (-s⁻¹.act x) (swath s x P)=P := by rw [swath_comp]; ext;simp [swath,affine]
lemma swell (P Q : Support n) (h : P⊆Q) : swath s x P⊆swath s x Q:= Finset.image_subset_image h
lemma s_sep (i j : Site n) : separation (affine s x i) (affine s x j) = separation i j:=by simp [affine]
lemma s_flags (τ : ℝ) (U : Config G n) : swath s x (flags τ (pull s x U))=flags τ U:= Work.H03.flags_send ..
lemma s_healthy (t : ℝ) (U : Config G n) (P : Support n) : Healthy t P (pull s x U) ↔ Healthy t (swath s x P) U := by
  unfold Healthy; rw [← s_flags s x t U]; exact (Finset.disjoint_image (sends s x).injective).symm
lemma swath_iffHalo (b : ℕ) (P : Support n) : swath s x (halo b P)=halo b (swath s x P) := by
  ext i
  obtain ⟨j,hq⟩:= (sends s x).surjective i
  have hi : affine s x j=i:=hq
  subst i; change (affine s x j∈swath _ _ _ ) ↔ _
  rw [stay]; simp_rw [halo_spec]
  constructor
  · rintro ⟨y,hy,hv⟩; exact ⟨_,(stay s x P).2 hy,(s_sep s x y j).trans_le hv⟩
  rintro ⟨y,hy,hv⟩; obtain ⟨a,ha,rfl⟩:=mem_image.mp hy
  exact ⟨_,ha,(s_sep s x a j).symm.trans_le hv⟩

lemma swath_cover (P : Support n) (b : ℕ) : coverNumber b (swath s x P)=coverNumber b P := by
  have he (s : Signed) (x : Site n) (P : Support n) : coverNumber b (swath s x P) ≤ coverNumber b P := by
    obtain ⟨D,⟨h₁,h₂⟩,ha⟩:=coverNumber_realized b P
    have hf : (swath s x D).card=D.card:=Finset.card_image_of_injective _ (sends s x).injective
    apply le_trans _ (hf.trans ha).le; apply list_cost
    unfold covers; dsimp only; rw [← swath_iffHalo]
    refine ⟨swell s x _ _ h₁,fun i hi j hj=> ?_⟩; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hj
    apply ReflTransGen.lift (r:= Touch (halo b D) 1) _ (by exact (fun a c h=> ⟨(stay s x _).2 h.1,(stay s x _).2 h.2.1,(s_sep ..).trans_le h.2.2⟩)) _ _ (h₂ i ((stay s x _).1 hi) j ((stay s x _).1 hj))
  have h:= he s⁻¹ (-s⁻¹.act x) (swath s x P)
  rw [swath_inv] at h;exact le_antisymm (he ..) h

-- For arbitrary signs, pull gauge remains gauge and pull locale preserves endpoint footprints.
lemma s_gauge (k : Site n→G.El) (U : Config G n) :
    pull s x (gauge k U)= gauge (k ∘ affine s x) (pull s x U) := by
  funext i; simp only [pull,Lattice.gauge, Function.comp_apply]
  have H := Step.gauge_read ((posDir i.2).rotate s) k U (affine s x i.1)
  have ht : affine s x (i.1+step i.2)= affine s x i.1+((posDir i.2).rotate s).vec := by
    rw [Step.vec_rotate,Step.vec_pos]; unfold affine; rw [Signed.act_add]; abel
  rw [ht];exact H

lemma s_locale (P : Support n) (U V : Config G n) (h : Agrees (swath s x P) U V) : Agrees P (pull s x U) (pull s x V) := by
  intro e he hp
  let d := (posDir e.2).rotate s; let y := affine s x e.1
  have hi : y∈ swath s x P:= mem_image_of_mem _ he
  have hg : y+d.vec ∈ swath s x P:= by
    rw [show y+d.vec=affine s x (e.1+step e.2) by dsimp only [d,y]; rw [Step.vec_rotate,Step.vec_pos];unfold affine; rw [Signed.act_add]; abel]
    exact mem_image_of_mem _ hp
  change d.read U y=d.read V y; generalize d=D at *
  rcases D with ⟨i,j|j⟩
  · exact h (y,i) hi hg
  change (U (y-step i,i))⁻¹=(V (y-step i,i))⁻¹
  rw [h]; exacts [by simpa [sub_eq_add_neg,Step.vec] using hg,by simpa using hi]
lemma p_local (P : Support n) {α : Type*} {F : Config G n→α} (h : LocalOn P F) : LocalOn (swath s x P) (F ∘ pull s x) := fun U V h₁=> h _ _ (s_locale s x P U V h₁)
lemma p_invar {α : Type*} {F : Config G n→α} (h : GaugeInvariant F) : GaugeInvariant (F ∘ pull s x) := by
  intro i U; rw [Function.comp_apply,s_gauge]; exact h ..
lemma final_swath (P : Support n) (b : ℝ) {α : Type*} {F : Config G n→α} (h : UsesFinal b P F) : UsesFinal b (swath s x P) (F ∘ pull s x) := by
  intro U V hx hf
  refine h _ _ (s_locale _ _ _ _ _ hx) ?_; apply (Finset.image_injective (sends s x).injective)
  rw [Finset.image_inter _ _ (sends s x).injective,Finset.image_inter _ _ (sends s x).injective]
  change swath s x P ∩ swath s x _=swath s x P ∩ swath s x _; rw [s_flags,s_flags];exact hf

-- ses flags monotone
omit s x in
lemma threshold (t u : ℝ) (h : t≤u) (U : Config G n) : flags u U⊆flags t U := by
  intro i hi; obtain ⟨j,hj,hz⟩:= (flags_spec ..).1 hi; exact (flags_spec t U _).2 ⟨j,hj,h.trans_lt hz⟩
omit s x in
lemma threshold_fit (t u : ℝ) (h : t≤u) (P : Support n) {U : Config G n} (hx : Healthy t P U) : Healthy u P U:= Finset.disjoint_left.mpr fun _ hp hv => Finset.disjoint_left.mp hx hp (threshold t u h _ hv)
lemma swath_here (v : ℕ) : swath s x (halo v {0})=halo v {x}:=by rw [swath_iffHalo]; simp [swath,affine]
end YM.Next.Rank.Thirst
