import YM.Trace.Measuring
import YM.Trace.Fields

/-!
An ensemble-aware phase choice for *weak engineering* comparisons only. The
smallness estimate retains the full positive ordered moment; the common
cluster limit is not being interchanged against the UV sequence. A bounded
translation of these Euclidean positions just changes the midpoint.
-/

set_option autoImplicit false
set_option maxRecDepth 12000
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

noncomputable section
namespace YM.Trace
open Maxwell Labels Table Next.UVStress Org Climb Function Filter Set OS Word Extraction Table.Pairing Complex MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {Q : MaxwellData C}
variable {V : DiffPlan S} {I : IR (C:=C) S} {H : Org.UV C f S V Q I} {c : ℝ} {U : ∀ d, Spin.change S d} {Y : S.Stress}

def ticking (s : ℝ) : Points 1 := points (fun _ => s • basis timeAxis)
def joined := Table.Pairing.closedUp timeAxis (ticking (2:ℝ)⁻¹) (ticking (2:ℝ)⁻¹)
lemma living_ticks {s : ℝ} (h : 0<s) : Pairing.single (s • ticking (2:ℝ)⁻¹) timeAxis :=
     ⟨fun _ _ _ => Subsingleton.elim .., fun i => by
       change 0 < s * ((2:ℝ)⁻¹ * (basis timeAxis timeAxis))
       simp [basis_eq]; positivity⟩
lemma uniting (s : ℝ) : s • joined = Pairing.closedUp timeAxis (s • ticking (2:ℝ)⁻¹) (s • ticking (2:ℝ)⁻¹) :=
     ((pairIso timeAxis (n:=1) (m:=1)).symm.map_smul s _).symm
lemma joined_free : joined ∈ conf 2 := by
   rw [← one_smul ℝ joined,uniting]; exact spans (living_ticks one_pos) (living_ticks one_pos)
abbrev frontCount (T : Table C.book) (s : ℝ) (q : S.Field 4) : ℂ :=
   (S.classMoment T (fun _ => 4) (s • joined)) fun _ => q

def energyLine (Y : Stress S) (s e : ℝ) := ((s^4:ℝ):ℂ) • withoutMean Y e
abbrev unlabel {n : ℕ} (q : S.Field 4) (_ : Fin n) : C.book.Token := ⟨4,S.representative 4 q⟩
lemma unlabel_eq {T : Table C.book} (h : T.Basic) (hr : T.respects S) {s : ℝ} (hs : 0<s) (q : S.Field 4) :
    frontCount T s q = T.read (s • joined) (unlabel q) := by
    rw [← S.at_project T h.toSymmetric hr (uniting s ▸ spans (living_ticks hs) (living_ticks hs))]
    change frontCount T s q = S.classMoment T (fun _ => 4) _ _
    exact congr_arg (fun u : Fin 2 → S.Field 4 => S.classMoment T (fun _ => 4) (s • joined) u) <| funext (fun t : Fin (1+1) => (S.rep 4 q).symm)

lemma trace_adjoint {h : S.RealSpin} {Z : Spec.Algebra S} (hL : Spec.Locals Z h) (s e : ℝ) :
    S.adj h 4 timeAxis (energyLine Z.energy s e) = energyLine Z.energy s e := by
    unfold energyLine
    simp only [map_smulₛₗ, conj_ofReal]
    have he : S.conj h 4 (withoutMean Z.energy e) = withoutMean Z.energy e := by
       unfold withoutMean; rw [map_sub,map_sum,map_smulₛₗ,S.conj_unit]; simp_rw [hL.conserved.real]; rw [conj_ofReal]
    change ((s^4:ℝ):ℂ) • S.mirror h 4 (Signed.mirror timeAxis) (S.conj _ _ _) = _
    rw [he,← hL.spots.signed 4, without_rotate _ _ hL.spots hL.spin]

-- test *full* word prior to taking ground character; each character reads the same classes.
lemma gram_value {T : Table C.book} (h : T.Basic) (hr : T.respects S) (H' : S.RealSpin) (X : Schwinger T timeAxis)
    {s : ℝ} (hs : 0<s) (q : S.Field 4) (hQ : S.adj H' 4 timeAxis q = q) :
    ∃ b : Future C.book timeAxis,  ((‖X.plant b‖^2:ℝ):ℂ) = frontCount (S:=S) T s q := by
    let w := unlabel q (n:=1); let x := s • ticking (2:ℝ)⁻¹
    have ht := living_ticks hs
    let b : Future C.book timeAxis := ⟨realize w x, Pairing.living w ht⟩
    have hv := displacement T h.toSymmetric w w ht ht
    have hf : (closedUp timeAxis x x)=s • joined := (uniting s).symm
    refine ⟨b, ?_⟩ -- maybe backwards
    trans T.read (s • joined) (tied w w timeAxis)
    · rw [← hf,← hv]
      change _ = T.gram timeAxis b.val b.val
      rw [← X.measure]
      push_cast; exact (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (X.plant b)).symm
    rw [← S.at_project T h.toSymmetric hr (hf ▸ spans ht ht)]; unfold frontCount
    suffices hk : S.classTokens ∘ tied w w timeAxis = fun _ => ⟨4,q⟩ by rw [hk]; rfl
    funext t
    refine Fin.addCases ?_ ?_ t
    · intro i; simp only [tied, Fin.append_left, comp_apply]
      change (⟨4,S.project 4 (C.book.adj _ timeAxis (S.representative _ q))⟩ : S.Tag) = Sigma.mk 4 q
      rw [← S.adj_project (H:=H'), S.rep, hQ]
    intro i; simp only [tied,Fin.append_right,comp_apply]
    change Sigma.mk 4 (S.project _ (S.representative _ _))=Sigma.mk 4 q
    rw [S.rep]

lemma raw_endpoint (hY : Tab S V Q I H c U Y) (hI : I.J≠0) (he : I.J∈KernelSpace H.basis.kernel.spin)
     (p : FreeDiv Q.T Q.hT Q.lit.hers) (X : Scaling S) (hX : Approaches (path X) (isoPanel X))
     (hS : Stable H.basis.kernel.spin Q.hT.spin V Q.T.W X) (hT : Q.T.J = UVNext.FreeStress.torch C.book.grid 1)
     (hQ : X.meter I.J Q.T.J) (hG : G.Simple) (e : ℝ) :
     Tendsto (fun k => (X.U k 4).symm (energyLine Y (X.r k) e)) atTop (𝓝 0) := by
    have hh := rawPayload_tendsto hY hI he p X hX hS hT hQ hG
    let Kval := expectation S 4 (sumTrace Y)-(↑e:ℂ)
    have hp : sumTrace Y - sumTrace (reCenter S Y)= expectation S 4 (sumTrace Y) • S.unit 4 := by
       rw [show sumTrace (reCenter S Y) = centering S 4 (sumTrace Y) from (map_sum (centering S 4) (fun i => Y i i) _).symm,
         value_center]; abel
    have he i : energyLine Y (X.r i) e = X.r i^4 • sumTrace (reCenter S Y) + X.r i^4 • Kval • S.unit 4 := by
       unfold energyLine; rw [Complex.coe_smul,← smul_add]; unfold withoutMean Kval sumTrace at *
       rw [sub_smul, ← hp]; abel
    have hb := (X.drips.pow 4).smul_const (Kval • (Bel C.book).unit 4)
    have hx i (z) : (X.U i 4).symm (X.r i ^4 • z) = X.r i^4 • ((X.U i 4).symm z) :=
       (((X.U i 4).symm.toLinearMap).restrictScalars ℝ).map_smul ..
    simp_rw [he,map_add,hx,map_smul]
    have ht0 := hh.add hb
    rw [show (0:ℝ)^4=0 by norm_num,zero_smul,zero_add] at ht0
    refine Tendsto.congr' ((hS.units 4).mono fun i hi => ?_) ht0
    rw [hx, ← hi]; dsimp only; rw [LinearEquiv.symm_apply_apply]

lemma pointwise_uv (X : Scaling S) (ht : Approaches (path X) (isoPanel X)) (H0 : S.Hierarchy) (h : V.Derivatives S)
   (K : (Bel C.book).Hierarchy) (W : DiffPlan (Bel C.book)) (hp : W.Derivatives (Bel C.book))
   {n : ℕ} (v : ℕ → Fin n → (Bel C.book).Field 4) (u : Fin n → (Bel C.book).Field 4)
   (hv : ∀ i, Tendsto (fun k => v k i) atTop (𝓝 (u i)))
   {x : Points n} (hx : x∈conf _) : Tendsto (fun k => (S.classMoment S (fun _ => 4) (X.r k • x)) (fun i => X.U k 4 (v k i)))
    atTop (𝓝 ((Bel C.book).classMoment (Bel C.book) (fun _ => 4) x u)) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    let t := fun _ : Fin n => 4
    filter_upwards [travels_jet H0 h K hp X ht (t:=t) v u hv 0 {x} isCompact_singleton (singleton_subset_iff.mpr hx) (ε/2) (by positivity)]
      with k hk
    have he := hk x rfl
    let Q := tested (X.r k) (isoPanel X k) (hang t (v k)); let Q0 := Ward.disc (hang (T:=Bel C.book) t u)
    change ‖iteratedFDeriv ℝ 0 Q x - iteratedFDeriv ℝ 0 Q0 x‖ ≤ _ at he
    rw [show iteratedFDeriv ℝ 0 Q x - iteratedFDeriv ℝ 0 Q0 x = iteratedFDeriv ℝ 0 (Q-Q0) x by ext1 y; simp,
       norm_iteratedFDeriv_zero] at he
    rw [dist_eq_norm]; unfold Table.classMoment
    exact he.trans_lt (half_lt_self hε)

lemma zero_uv (hY : Tab S V Q I H c U Y) (X : Scaling S) (hX : Approaches (path X) (isoPanel X))
     (y : ℕ → S.Field 4) (h : Tendsto (fun k => (X.U k 4).symm (y k)) atTop (𝓝 0)) {x : Points 2} (hx : x∈conf _) :
     Tendsto (fun k => (S.classMoment S (fun _ => 4) (X.r k • x)) (fun _ => y k)) atTop (𝓝 0) := by
   have he := pointwise_uv X hX H.basis.kernel hY.locality.derivatives Q.hT Q.T.W Q.lit.pales
      (fun k _ => (X.U k 4).symm (y k)) 0 (fun _ => h) hx
   let W := Bel C.book
   simpa [show W.classMoment W (fun _ : Fin 2 => 4) x 0=0 from MultilinearMap.map_coord_zero _ (0:Fin 2) rfl]
      using he
end YM.Trace
namespace YM.Trace
open Maxwell Labels Table Next.UVStress Org Org.Phase Climb Function Filter Set OS OS.Ground Word Extraction Complex MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal RealInnerProductSpace
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {Q : MaxwellData C}
     {V : DiffPlan S} {I : IR (C:=C) S} {H : Org.UV C f S V Q I} {c : ℝ} {U : ∀ d, Spin.change S d} {Y : S.Stress}
private lemma ae_small {X : Type*} [MeasurableSpace X] {μ : Measure X} (h : ℕ → X → ℝ) (heq : ∀ i x, 0 ≤ h i x)
  (hi : ∀ i, Integrable (h i) μ) (hv : Tendsto (fun i=>∫ x,h i x∂μ) atTop (𝓝 0)) : ∃ n : ℕ → ℕ, StrictMono n ∧
     ∀ᵐ x∂μ,Tendsto (fun j => h (n j) x) atTop (𝓝 0) := by
   have ht i : eLpNorm (h i) 1 μ = ENNReal.ofReal (∫ x, h i x∂μ) := by
       rw [ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ (heq i)),eLpNorm_one_eq_lintegral_enorm]
       simp [(Real.enorm_of_nonneg (heq i _))]
   exact (tendstoInMeasure_of_tendsto_eLpNorm (p:=1) (g:=0) one_ne_zero (fun i=>(hi i).1) aestronglyMeasurable_zero
     (show Tendsto _ _ _ by simpa only [sub_zero,ht,ENNReal.ofReal_zero] using! ENNReal.continuous_ofReal.continuousAt (x:=0)|>.tendsto.comp hv)
     |>.exists_seq_tendsto_ae)

lemma polynomial (J : Stress S) (T : Table C.book) (s e : ℝ) : let E (e : ℝ):= frontCount T s (energyLine J s e);
      E e = (1-(e:ℂ)^2)*E 0+(((e:ℂ)^2+e)/2)*E 1 + (((e:ℂ)^2 -e)/2) * E (-1) := by
   intro E
   let L (u v : S.Field 4):= S.classMoment T (fun _ => 4) (s • joined) ![u,v]
   let a := ((s^4:ℝ):ℂ) • sumTrace J; let b := ((s^4:ℝ):ℂ) • S.unit 4
   have ht : energyLine J s=(fun e : ℝ => a-(e:ℂ) • b) := funext fun e => Eq.trans (smul_sub (↑(s^4:ℝ):ℂ) _ _) (by
      change ((s^4:ℝ):ℂ) • sumTrace J - ((s^4:ℝ):ℂ) • ((e:ℂ) • S.unit 4) = _; rw [smul_comm (e:ℂ)]) -- smul real vs complex
   have he (u v w y : S.Field 4) : L (u-v) (w-y)=L u w-L u y-(L v w-L v y) := by
     unfold L
     have g0 (k j l:S.Field 4): update ![k,j] 0 l=![l,j] := by ext i; fin_cases i <;> simp
     have g1 (k j l:S.Field 4): update ![k,j] 1 l=![k,l] := by ext i; fin_cases i <;> simp
     rw [← g0 u (w-y) (u-v), MultilinearMap.map_update_sub]
     simp_rw [g0]
     rw [← g1 u w (w-y), MultilinearMap.map_update_sub,g1,g1,
          ← g1 v w (w-y), MultilinearMap.map_update_sub,g1,g1]
   have h0 u v w (c : ℂ) : update (![u,v]:Fin 2→S.Field 4) (0:Fin 2) w=![w,v] := by ext x; fin_cases x <;> simp
   have h1 u v w (c : ℂ) : update (![u,v]:Fin 2→S.Field 4) (1:Fin 2) w=![u,w] := by ext x; fin_cases x <;> simp
   have hb (v w : S.Field 4) (c d : ℂ) : L (c • v) (d • w)= c*d*L v w := by
       unfold L
       rw [← h0 v _ _ c, MultilinearMap.map_update_smul,h0 v _ v c, ← h1 _ w _ d, MultilinearMap.map_update_smul,h1 v w w d]; simp; ring
   have hp (e : ℝ) : E e = L a a-(e:ℂ) * L a b - ((e:ℂ) * L b a-(e:ℂ)*(e:ℂ)*L b b) := by
       unfold E frontCount; rw [ht,show (fun _ : Fin 2=>a-(e:ℂ)•b)=![a-(e:ℂ)•b,a-(e:ℂ)•b] from by ext x; fin_cases x <;> rfl]
       change L _ _ = _
       rw [he,show L a ((e:ℂ) • b)= (e:ℂ)*L a b by simpa using hb a b 1 e,
          show L ((e:ℂ) • b) a=(e:ℂ)*L b a by simpa using hb b a e 1, hb b b e e]
   simp_rw [hp]; push_cast; ring

lemma submits (J : Spec.Algebra S) (hJ : Spec.Locals J H.basis.kernel.spin) (V₀ : OS.Chamber S timeAxis) (A : Spread V₀) (R : A.Resolution)
   (p : States V₀ A R) (hp : Scripts J V₀ A R p) (hR : R.Out) (X : Scaling S)
   (hz : ∀ e : ℝ, Tendsto (fun k => (X.U k 4).symm (energyLine J.energy (X.r k) e)) atTop (𝓝 0))
   (hXK : ∀ (y : ℕ → S.Field 4), Tendsto (fun i => (X.U i 4).symm (y i)) atTop (𝓝 0) →
     Tendsto (fun k=>frontCount S (X.r k) (y k)) atTop (𝓝 0)) : ∃ q : ℕ → ℕ, StrictMono q ∧
     ∀ᵐ x ∂ R.μ, ∀ e : ℝ, Tendsto (fun i => frontCount (p x) (X.r (q i)) (energyLine J.energy (X.r (q i)) e))
       atTop (𝓝 0) := by
   letI hμ := hR.normalized
   let z (e : ℝ) (k : ℕ) : S.Field 4 := energyLine J.energy (X.r k) e
   let t (e : ℝ) (k : ℕ) (i : R.X) := frontCount (p i) (X.r k) (z e k)
   have hf (e : ℝ) (k : ℕ) (w : R.X) : (t e k w).re ≥ 0 ∧ (t e k w).im=0 := by
     let D := Classical.choice (OS.realization (hp.loci w) timeAxis)
     obtain ⟨b,hb⟩ := gram_value (hp.loci w).laws (hp.sees w) H.basis.kernel.spin D.GNS (X.positive k) (z e k) (trace_adjoint hJ _ _)
     unfold t; erw [← hb]; exact ⟨sq_nonneg _,(ofReal_im _)⟩
   let data (e : ℝ) (k : ℕ) := realize (unlabel (z e k)) (X.r k • joined)
   have hd e k : Word.distinct (data e k) := (realized ..).mpr <| Work.A05.smul_conf (X.positive k) joined_free
   have hm e k x : t e k x = (p x).expect (data e k) := by
       unfold data; rw [(p x).readAt]; exact unlabel_eq (hp.loci x).laws (hp.sees x) (X.positive _) _
   have he (e k) : Continuous (t e k) := by
       have he : t e k = fun i => R.character i (M A _ (hd e k)) := funext fun i=> (hm e k i).trans (Cluster.track A _ (hd ..) i (hp.reads i))
       rw [he]; exact hR.weak _
   have hi e k : Integrable (t e k) R.μ := (he e k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hn e k : (∫ i, t e k i∂ R.μ)=frontCount S (X.r k) (z e k) := by
      have hh : S.expect (data e k)=frontCount S (X.r k) (z e k) := by
         unfold data; rw [S.readAt]; exact (unlabel_eq H.basis.kernel.laws (fun _=>le_rfl) (X.positive _) _).symm
      rw [show t e k = (fun i=> (p i).expect (data e k)) by exact funext (hm e k)];
      rw [R.barycenter p hR hp.reads H.basis.kernel.translations _ (hd ..),hh]
   have heq e : Tendsto (fun k => ∫ i, (t e k i).re∂ R.μ) atTop (𝓝 0) := by
      refine (show Tendsto (fun k => (frontCount S (X.r k) (z e k)).re) _ (𝓝 0) from
        continuous_re.continuousAt.tendsto.comp (hXK _ (hz e))).congr fun k => ?_
      exact congr_arg re (hn e k).symm |>.trans (integral_re (hi ..)).symm
   let E (k : ℕ) (i : R.X) := (t (-1) k i).re + (t 0 k i).re + (t 1 k i).re
   have hm e k:= (hi e k).re
   obtain ⟨n,hn,hN⟩ := ae_small E (by intro n i; exact add_nonneg (add_nonneg (hf .. |>.1) (hf .. |>.1)) (hf .. |>.1))
     (fun k => ((hm _ k).add (hm _ _)).add (hm _ _)) (show Tendsto _ _ _ by
       refine (show Tendsto _ _ _ by simpa only [add_zero] using ((heq (-1)).add (heq 0)).add (heq 1)).congr (by
         intro k; unfold E; erw [integral_add ((hm _ _).add (hm _ _)) (hm _ _),integral_add (hm _ _) (hm _ _)]; rfl))
   refine ⟨n,hn,?_⟩
   filter_upwards [hN] with i hI; intro e
   have hz u (hu : u= -1∨u=1∨u=0) : Tendsto (fun k => t u (n k) i) atTop (𝓝 0) := by
       have hb : Tendsto (fun k => (t u (n k) i).re) atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hI
         (fun _k => (hf ..).1) (fun k=>by
          rcases hu with h|h|h
          all_goals subst u; exact show _ ≤ (E _ _) from by unfold E; linarith [(hf (-1) (n k) i).1,(hf 0 (n k) i).1,(hf 1 (n k) i).1])
       have he := continuous_ofReal.continuousAt.tendsto.comp hb
       rw [Complex.ofReal_zero] at he
       refine Tendsto.congr (f₁:=fun k=> ((t u (n k) i).re:ℂ)) (fun k => Complex.ext rfl ?_) he
       exact (show 0 = (t u (n k) i).im from (hf ..).2.symm)
   simp_rw [polynomial J.energy (p i) _ e]
   simpa only [t,add_zero,mul_zero] using (((hz 0 (Or.inr (Or.inr rfl))).const_mul (1-(e:ℂ)^2)).add
       ((hz 1 (Or.inr (Or.inl rfl))).const_mul (((e:ℂ)^2+e)/2))).add ((hz (-1) (Or.inl rfl)).const_mul (((e:ℂ)^2 -e)/2))
end YM.Trace
