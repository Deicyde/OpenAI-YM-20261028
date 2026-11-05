import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Enrolled
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Metering
import YM.Next.BOUNDARY.Decomposition
import YM.Push.FREE_RESOLVENT.Metric

/-!
# Exact exponential cover for E Pcond on common families

Produces simultaneously for fixed kernel inputs, not just a storage
convention selected on each period. Post L (& eligible stage steps).
Translated periods use residues and positive plaquette base sites,
overlapping with support-halos for *both* covariance endpoints. Estimate
also includes true-length cuts even when period small. Can choose signed
indices/tags consistently or use all; harmonic included.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Current
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix Pressure
open Bid FreeResolvent Bloch Laurent Work.F08
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f : Side} (P : Patch) (K : KernelChoices) (F : Forest (nativeStep P K three).ratio) (G : Gauge)

lemma reserve {H : FaceRow} {s M a : ℝ} (h : P.Branches K G) (ha : 0<a) (hs : 0<s) (hM : 0≤M)
    (he : H.strip s M) (hg : ∀ f : Side, Gap (H.acts f) a) (n : Side) :
    Gap ((common P K F G H).acts n) (treeFare G P K a) := by
  have hh := common_price P K F G hs.le hM he
  apply cofinal_prices _ (Row.rights _ _ hh hs.le) _ (100*macroR P+3) _ n
  intro n hn
  have hw : 3 ≤ n.val := by omega
  let S := nativeStep P K n
  have hy : Larger (G:=G) S := ⟨h,by change 100*macroR _ ≤ n.val*P.L.val
                                     exact (show 100*macroR P≤n.val by omega).trans (Nat.le_mul_of_pos_right _ P.L.pos), by omega⟩
  have ht := (tree_gap S (spread P K F) H hy ha (hg _))
  let v := link P K F G hw
  have hp := ht.submatrix v.symm v.symm.injective
  change Gap ((treeMatrix G (nativeStep P K n) _ H).submatrix v.symm v.symm) _ at hp
  rw [enrolled P K F G n hw hs.le he] at hp
  simpa [v] using hp

section Bind

def dial := Co P.L (PAC G 2)
instance instDia : Fintype (dial P G) := inferInstanceAs (Fintype (Co P.L (PAC G 2)))
instance diaDecide : DecidableEq (dial P G) := inferInstanceAs (DecidableEq (Co P.L (PAC G 2)))

def rootMeter : Row (dial P G) (Asked P K F G) := fun i j => deck G P (cobound 1) i j.val
def mirrorPrice (s : ℝ) := (Fintype.card (TypeFace 1) : ℝ)*(cobound_ready 1 s).choose
lemma mirrorFee (s : ℝ) : 0≤mirrorPrice s := mul_nonneg (by positivity) (cobound_ready 1 s).choose_spec.1
lemma meter_width {s : ℝ} (hs : 0≤s) : (rootMeter P K F G).strip s (mirrorPrice s) := by
  obtain ⟨h,he⟩ := (cobound_ready 1 s).choose_spec
  exact fun i j => deck_strip _ hs h he _ j.val
lemma meter_reads (n : Side) (hn : 3≤n.val) :
    let S:=nativeStep P K n
    plane (G:=G) S (spread P K F)= ((rootMeter P K F G).acts n).submatrix
      (splitCo S.ratio (PAC G 2)) (link P K F G hn) := by
  intro S
  rw [plane_sub]; obtain ⟨h, he⟩ := (cobound_ready 1 (0:ℝ)).choose_spec; change (tensor G ((cobound 1).acts _)).submatrix id _ = _; rw [deck_values G S (le_refl (0:ℝ)) he]; ext; rfl




/-- All-period frequent supply (L fixed first, odd as needed for
issuing the stage). For now F also chosen (one template at three-period
cover); below choose it from patch. Don't require Towers to satisfy on ALL
periods: the ticket for publishing is on H, no crossing at ineligible sizes. -/
theorem earned (s M a : ℝ) (h : P.Branches K G) (ha : 0<a) (hs : 0<s) (hM : 0≤M) :
    ∃ t A : ℝ, 0<t ∧ 0<A ∧ ∀ {H : Bed}, H.metric.strip s M →
      (∀ f : Side, Gap (H.metric.acts f) a) →
      ∃ Z : Row (dial P G) (dial P G), Z.strip t A ∧
        (∀ n : Side, ∀ _hn : 3≤n.val, ((Z.acts n).submatrix (splitCo (nativeStep P K n).ratio (PAC G 2)) (splitCo (nativeStep P K n).ratio (PAC G 2)))=
          plane (G:=G) (nativeStep P K n) (spread P K F) * treeInverse G (nativeStep P K n) (spread P K F) H.metric 0*
          (plane (G:=G) (nativeStep P K n) (spread P K F)).transpose) := by
  let r := treeFare G P K a; have hr : 0<r := treeFare_pos G P K ha
  let V := outputPrice P K.penalty s M; have hv : 0≤V := outputPrice_nn P _ s M hM
  let w := margin (Asked P K F G) s V r; have hw : 0<w := margin_pos _ hs hv hr
  let t := min (w/2) s; have ht : 0<t := lt_min (half_pos hw) hs
  let l := inversePrice (Asked P K F G) s V r 0 t
  have hl : 0<l := inversePrice_pos (α:=Asked P K F G) le_rfl hr ((min_le_left ..).trans_lt (half_lt_self hw))
  let C:=(Fintype.card (Asked P K F G):ℝ); let A:=mirrorPrice t
  let X := C*((C*(A*l))*A); have hx : 0≤X := by have hh : 0≤A := mirrorFee _; unfold X C; positivity
  refine ⟨t,X+1,ht,by linarith,?_⟩
  intro H hh hd
  let Q:=common P K F G H.metric
  have hq : Q.strip s V := common_price P K F G hs.le hM hh
  obtain ⟨J,hJ,hg⟩ := strip_resolvent Q (M:=V) (r:=r) (u:=0) (γ:=t) le_rfl hr hs hv hq (reserve P K F G h ha hs hM hh hd) ((min_le_left ..).trans_lt (half_lt_self hw))
  let D := rootMeter P K F G; have hb : D.strip t A := meter_width _ _ _ _ ht.le
  let B := composeRows D J
  let Z := composeRows B (transRows D)
  have he : Z.strip t X := strip_compose ht.le (strip_compose ht.le hb hJ) (strip_trans hb)
  refine ⟨Z,strip_mono he le_rfl (le_add_of_nonneg_right zero_le_one), fun n hn => ?_⟩
  let S := nativeStep P K n
  let f := splitCo S.ratio (PAC G 2)
  let v := link P K F G hn
  let j := resolve (Q.acts n) 0
  have htZ : Z.acts n = D.acts n*j*(D.acts n).transpose := by
    rw [show Z=composeRows B (transRows D) from rfl,acts_compose ht.le (strip_compose ht.le hb hJ) (strip_trans hb), acts_trans,acts_compose ht.le hb hJ,hg]
  have hp : plane S (spread P K F)=(D.acts n).submatrix f v := meter_reads P K F G n hn
  change ((Z.acts n).submatrix (splitCo S.ratio (PAC G 2)) (splitCo S.ratio _))=plane (G:=G) S (spread P K F) * treeInverse G S (spread P K F) H.metric 0 * (plane (G:=G) S (spread P K F)).transpose
  rw [hp]
  have hj : treeInverse G S (spread P K F) H.metric 0=j.submatrix v v := by
    unfold treeInverse j resolve; rw [zero_smul,add_zero]; simp only [zero_smul,add_zero]; erw [enrolled P K F G n hn hs.le hh,inverse_reindex _ v]
  rw [htZ,hj,Matrix.submatrix_mul_equiv,transpose_submatrix,Matrix.submatrix_mul_equiv]
end Bind

/-- True simultaneous cover lift and cut (including all period comparisons
when the crossing identities are supplied on those periods--harmonic true).
The representation is translation-periodic in **coarse cell** counts;
the phases/residue offsets were not silently pitched to site translations
or plaquette midpoints. This cut is in coarse cell BASE displacement, not
asserted invariant under reorientation, and checks every periodic image.
Consumers needing signed cuts can also use the exponential tail estimate
on complement of any rule keeping at least these addresses. -/
theorem onePlateau (s M a : ℝ) (hL : Odd P.L.val) (h : P.Branches K G) (ha : 0<a) (hs : 0<s) (hM : 0≤M) :
    ∃ t A : ℝ, 0<t ∧ 0<A ∧ ∀ {H : Bed} {p : Clip} {v : ℝ}, H.metric.strip s M →
      (∀ f : Side, Floor H p f a v) →
      ∃ Z : Row (dial P G) (dial P G), Z.strip t A ∧
        (∀ {c f : Side} (S : StepData c f) (hp : S.patch=P),
          let g := (S.ratio : Ratio c f); let b1 : g.count = P.L := congr_arg Patch.L hp;
          let E := (splitCo g (PAC G 2)).trans (Equiv.prodCongr (Equiv.refl (Site c)) (Equiv.cast (congr_arg (fun L => Co L (PAC G 2)) b1)))
          S.kernel=K → Larger (G:=G) S → 3 ≤ c.val →
          ∀ (B : Bed) (T : Towers S.patch.L) (C : Clip) (m W : ℝ), 0 < m → Floor B C c m W → Towers.Diagonal S H B T →
            (Z.acts c).submatrix E E=tensor G (fConditional S H B T)) ∧
        (∀ d : ℕ, (minusRows Z (shorten d Z)).strip (t/2) (Real.exp (-t/2*d)*A)) := by
  let F := Classical.choice (Tree.select (nativeStep P K three).ratio (by exact hL))
  obtain ⟨t,A,ht,hA,hw⟩ := earned P K F G s M a h ha hs hM
  refine ⟨t,A,ht,hA,?_⟩; intro H p v he hh
  obtain ⟨Z,hZ,HZ⟩ := hw he (fun f => ⟨fun w => ((hh f).uniform.1 w).1⟩)
  refine ⟨Z,hZ,fun {c f} S hp => ?_,fun d => ?_⟩
  · intro g b1 E hK hy hn B T C m W hx H Hf
    have hf : f=c*P.L := by
      apply Subtype.ext; exact S.sizes.trans (by rw [hp]; rfl)
    subst f; rcases S with ⟨vT,k,hS⟩; have hl : vT=P := hp; subst vT; have hi : k=K := hK; subst k
    exact (HZ c hn).trans (cutHead _ (spread P K F) _ hy (hh _) ha T H hx Hf)
  have he := strip_tail hZ d (half_le_self ht.le)
  rw [show t/2-t= -t/2 by ring] at he; exact he
end YM.AnalyticBridge.LocalGaussianLaws.Current
