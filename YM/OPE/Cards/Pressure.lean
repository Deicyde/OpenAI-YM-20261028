import YM.OPE.Cards.Mix
import YM.Work.B17

/-!
# Deck witness and character bound

No inner order limits for the varying matcher label are necessary. It is
extracted along a refinement of the filter that tests all point fields;
at each individual pair of regulators use a static `Episode` of that
cutoff's labels. Therefore `B17` can be consumed as-is while comparing two
separate choices of episode with the same itinerary. Then invoke abelian
ground functional calculus on the actual law.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cards
open Function Filter Set Lattice Cells Wilson Extraction Word Next.Phase
open Work Next.Rank Station Bid
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{C:Family G} {ι κ : Type}[Fintype ι][Fintype κ] {S: Table C.book}
    {φ : Extraction.Order} {𝓕 : Filter (ℕ×ℕ)}
variable {N p k k' b l f n q Q : ℕ} {B:ι→ℝ}{D:κ→ℝ}
    (e:b≤ k)(t m:ℕ) {x:ι→ Cover}{y:κ→ Cover}

lemma variation {d:Caps n} (b : Fin n→ Cover)(h:φ.PointLimits C S)(hb:Extraction.Order.grid C k b ∈ generic _)(p : C.book.Vector d)(w : ℕ×ℕ → C.book.Vector d) (hp:∀ i,Tendsto (fun v=> w v i) 𝓕 (𝓝 (p i))) (ht:𝓕 ≤ φ.fuse) : Tendsto
      (fun i:ℕ×ℕ => C.ensemble d (fun j => location C.S k i.1 i.2 (b j)) (w i)) 𝓕
      (𝓝 (S.value d (Extraction.Order.grid C k b) p)):=by
    -- See `when_varying` in Cells/Transforms.
    let E (i) := dial (L:= C.book) d i
    let J := (i:Fin n)→ (C.book.coord (d i)).Index; letI : Fintype J:= Pi.instFintype; let Y(r:J) i:= E i (r i); let W(F:C.book.Vector d)(r:J):= ∏ i,(E i).repr (F i) (r i)
    have he(X:Moment C.book n d)(t:C.book.Vector d): X t=∑ j:J,W t j*X (Y j):=by
       have hx:t= fun i=> ∑ k,(E i).repr (t i) k • E i k:= funext fun i=> ((E i).sum_repr _).symm
       conv_lhs=> rw [hx]
       rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl (fun j _=> X.map_smul_univ (fun k=>(E k).repr (t k) (j k)) _)
    have hS(t:J): Tendsto (fun i:ℕ×ℕ=> C.ensemble d (fun j=> location C.S k i.1 i.2 (b j)) (Y t)) 𝓕
       (𝓝 (S.value d (Extraction.Order.grid C k b) (Y t))) := (Extraction.Order.along (eventual_grid C φ S h b hb (fun i=> ⟨d i,Y t i⟩))).mono_left ht
    have hW(t:J):Tendsto (fun i:ℕ×ℕ => W (w i) t) 𝓕 (𝓝 (W p t)):= tendsto_finsetProd _ (fun k _=> ((E k).coord (t k)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hp k))
    rw [he (S.value ..)]; exact (tendsto_finsetSum Finset.univ (fun i _=> (hW i).mul (hS i))).congr' (Eventually.of_forall fun i=> (he (C.ensemble d (fun j=> location C.S k i.1 i.2 (b j))) (w i)).symm)

variable (E:Episode C φ k)
abbrev Moving (E:Episode C φ k) := (i : Fin E.num)→ (j: Fin (E.image i)) → ℕ×ℕ → C.label (E.weight i j)
-- remove dummy

variable (Y: Moving E)
def edition (c : ℕ×ℕ): Episode C φ k where
    num:= E.num
    factor := E.factor
    image := E.image
    seats := E.seats
    gen := E.gen
    weight := E.weight
    current := fun i j _ _=>Y i j c
    point := fun i j=>Y i j c
    views := fun i j => ⟨by simp, fun _=> Y i j c,fun _ _=>tendsto_const_nhds,tendsto_const_nhds⟩
def editorial : Cylinder C := fun N p U => (edition E Y (N,p)).cuts N p 0 U

def travel (𝓕 : Filter (ℕ×ℕ)) : Prop:= ∀ i j,Tendsto (Y i j) 𝓕 (𝓝 (E.point i j))
variable (h:C.Makes)(hr:𝓕 ≤ φ.fuse)
include h hr
lemma edition_bill : ∀ᶠ i : ℕ×ℕ in 𝓕, deck C e m t (editorial E Y) i.1 i.2 =
    ∑ j : Fin (2*m)→ Fin E.num, E.price m j * moment (C.beta i.1 i.2) (B16.term (edition E Y i) j e t i.1 i.2):=by
    have he: ∀ᶠ c : ℕ × ℕ in 𝓕, ∀ a q,C.ref (E.weight a q) ≤ c.1:= eventually_all.mpr fun i=> eventually_all.mpr fun j=> ((largeMesh φ).eventually_ge_atTop _).filter_mono hr
    filter_upwards [he] with i hi; let E':= edition E Y i; let N:=i.1; let p:=i.2
    have hE: deck C e m t (editorial E Y) i.1 i.2=E'.fromCut e t m i.1 i.2:=by unfold deck editorial; simp_rw [comp_apply, B15.cuts_translate]; rfl
    rw [hE]; change E'.fromCut e t m N p=∑ j:Fin (2*m) → Fin E'.num, E'.price m j * moment (C.beta N p) (B16.term E' j e t N p)
    dsimp only [Episode.fromCut,moment]; simp_rw [B16.twice_expand E' h e m t N p hi]; rw [MeasureTheory.integral_finsetSum]; simp_rw [MeasureTheory.integral_const_mul];
    exact fun i _=> continuous_integrable (C.beta N p) (continuous_const.mul (B16.term_cont E' i e t N p))
omit h in
lemma replicaTerm (ht:φ.PointLimits C S) (hp: travel E Y 𝓕) (j:Fin (2*m) → Fin E.num) :
    ∀ᶠ t in atTop,Tendsto (fun i:ℕ×ℕ=> moment (C.beta i.1 i.2) (B16.term (edition E Y i) j e t i.1 i.2)) 𝓕 (𝓝 (S.expect (E.flick e t m j))) :=by
    filter_upwards [B16.translate_generic E j e] with t he; rw [B16.flick_realized,Table.readAt]; let u a:= (B16.slots E j).get a; let d a:= B16.gradeSlot E j (u a)
    let X (i:ℕ×ℕ) (a:Fin (B16.slots E j).length) : C.label (d a):= if (u a).1.val%2=0 then star (Y _ (u a).2 i) else Y _ (u a).2 i
    have hx(a): Tendsto (fun i=>X i a) 𝓕 (𝓝 (B16.labelSlot E j (u a))) := by unfold X B16.labelSlot; split; exact (hp ..).star; exact hp ..
    apply variation (fun a=> B16.placeSlot E j e t (u a)) ht he (d:=d) (fun a=> B16.labelSlot E j (u a)) X hx hr -- maybe exact fixes
lemma deck_limit (ht:φ.PointLimits C S)(hp: travel E Y 𝓕) : ∀ᶠ t : ℕ in atTop, Tendsto (fun i : ℕ×ℕ=>deck C e m t (editorial E Y) i.1 i.2) 𝓕
     (𝓝 (E.wanted e t m S)):=by
    filter_upwards [eventually_all.mpr (replicaTerm (C:=C) e m E Y hr ht hp)] with t ht; exact Tendsto.congr' ((edition_bill e t m E Y h hr).mono fun _ hc=>hc.symm)
       (tendsto_finsetSum _ (fun i _=> tendsto_const_nhds.mul (ht i)))
omit h hr
open OS Ground Spec WeakDual Extraction.Retain
variable {V : Chamber S timeAxis}{A : Spread V}{R: A.Resolution} {c : ℝ}
-- Might need explicit norm structure; avoid diam.
private lemma pressure_in {X:Type*}[CommCStarAlgebra X] (u:X)(hc:0≤c): ‖u‖ ≤ c ↔ ∀ p : X →⋆ₐ[ℂ] ℂ, ‖p u‖ ≤ c:=by
    have hp : ‖u‖ = ‖gelfandTransform ℂ X u‖:= ((gelfandTransform_isometry X).norm_map_of_map_zero (map_zero _) _).symm
    rw [hp,ContinuousMap.norm_le _ hc]
    refine ⟨fun h p=>?_,fun h i=>?_⟩
    · obtain ⟨x,rfl⟩:= Ground.bij.2 p; exact h _
    exact h (Ground.view i)
lemma pressure (hi:R.Out)(u:A.algebra)(hc:0≤c): ‖u‖ ≤ c ↔ ∀ i:R.X, ‖R.character i u‖ ≤ c:=by
    have ab:=hi.abelian; haveI : IsClosed (A.algebra : Set V.VacuumOp):= isClosed_closure
    letI : CommCStarAlgebra A.algebra := { (StarSubalgebra.cstarAlgebra A.algebra) with mul_comm:=ab }
    rw [pressure_in u hc]; refine ⟨fun h i=>h _,fun h q=>?_⟩; obtain ⟨i,rfl⟩:=hi.onto.2 q; exact h _
lemma pressure_character (hi:R.Out)(u:A.algebra)(x:R.X): ‖R.character x u‖ ≤ ‖u‖:= (pressure hi u (norm_nonneg _)).mp le_rfl x
variable (Y' : Seed C φ S) (ht : Theme V A) (he : Steady V) (hp : Org.Phase.reflects (C:=C) V A)
include Y' ht he hp hr
/-- Includes every letter in the episode, with the cluster discrepancies sold
under the *whole polynomial* budget. -/
theorem carrying [𝓕.NeBot] (hi:R.Out)(hc:0≤c)(hY:travel E Y 𝓕)
    (hF:∀ m : ℕ, ∀ᶠ t : ℕ in atTop, ∀ᶠ i in 𝓕, ‖deck C e m t (editorial E Y) i.1 i.2‖ ≤ c^(2*m)) :
    ‖E.cluster A‖ ≤ c :=by
    apply (pressure hi _ hc).2; apply bit A hi _ _ hc; intro m
    refine le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp (B17.answer Y' V A ht he hp b k e E m)) ?_
    filter_upwards [deck_limit e m E Y Y'.cutoff hr Y'.generic hY,hF m] with t hN hS
    exact le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hN) (hS.mono fun i H=> (Complex.re_le_norm _).trans H)
end YM.OPE.Cards
