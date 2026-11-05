import YM.Push.CORRECTED_COLUMNS.Integrals
import YM.SectorNext.VACUUM_NORMALIZATION.Composition
import YM.SectorNext.VACUUM_NORMALIZATION.Thermal

/-!
# Triangular probes with missing rows

Before Gaussian, for  noise and seed masks (
technique, here at profile scale). At fixed V, the coarse rotation variables
only replace site-count (minus one) of the missing fine pivots. No reliance
on any across-period determinant commutation. n≥2 payment (including n=2)
only, and a one-dimensional Haar probe always in real Color units. No
claim that THESE triangular rows fit simultaneously with an arbitrary block
trunk order on the same lattice (they don't need to for our uses).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Lattice RG Wilson Function Set Filter Tree Finset MeasureTheory
set_option maxHeartbeats 400000
open SectorNext.Vacuum Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
open Push.Corrected.Torus (E paid howmany rim_count index eliminates reads chosen_product arrives length grows enters_once)
variable {G : Gauge} {n : Side}

local notation "Δ" => Module.finrank ℝ G.Color
lemma sip (G : Gauge) : ∃ K : ℝ, 1 ≤ K ∧ ∀ t,0<t → t ≤ 1 →
    (∫ x,draught t⁻¹ x ∂G.probHaar) ≤ K*t^(Module.finrank ℝ G.Color) := by
  obtain ⟨q,hq,H⟩ := chord_z (Next.Foundations.chart G) (Next.Foundations.chart_ok G) 1 zero_lt_one
  refine ⟨max 1 q,le_max_left ..,fun t ht hh => ?_⟩
  let d := Module.finrank ℝ G.Color
  have he := H t⁻¹ (by simpa only [inv_one] using inv_anti₀ ht hh)
  simp only [mul_one] at he
  have hr := mul_le_mul_of_nonneg_left he (a:=t^d) (by positivity)
  rw [←mul_assoc (t^d),inv_pow,mul_inv_cancel₀ (by positivity),one_mul] at hr
  exact hr.trans (by rw [mul_comm]; gcongr; exact le_max_right ..)

def ration (I : Finset (Cell n)) (t : ℝ) (U : Config G n) :=
    ∏ i∈Iᶜ,draught t⁻¹ (faceValue U i)
lemma ration_cont (I : Finset (Cell n)) (t : ℝ) : Continuous (ration (G:=G) I t) := by
  unfold ration draught faceValue; fun_prop
lemma ration_GI (I : Finset (Cell n)) (t : ℝ) : GaugeInvariant (ration (G:=G) I t) := by
  intro k U; unfold ration draught; simp only [face_gauge,G.chord_conj]
lemma ration_nonneg (I : Finset (Cell n)) (t : ℝ) (U : Config G n) : 0 ≤ ration I t U := by
  unfold ration; exact prod_nonneg fun i _ => (Real.exp_pos _).le

private lemma per_hole (i v d j : ℕ) (K t : ℝ) (hK : 1 ≤ K) (ht : 0<t) (hh : t≤1)
    (h1 : i ≤ v) (h2 : v ≤ i+j) : (K*t^d)^i ≤ (K*t^d)^v*(t⁻¹^d)^j := by
  have he : K^i≤K^v := pow_le_pow_right₀ hK h1
  calc
    _ ≤ K^v * (t^d)^i := by rw [mul_pow]; gcongr
    _ ≤ _ := by
      rw [mul_pow,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [inv_pow,inv_pow,← div_eq_mul_inv,le_div_iff₀ (by positivity),← pow_add]
      exact pow_le_pow_of_le_one (by positivity) (pow_le_one₀ ht.le hh) h2

/-- Fine default masks pay at least this many plaquette pivots even in a
single booked sector. No multiplicity for winding paths. -/
lemma pruned_default (hn : 2≤n.val) (I : Finset (Cell n)) (t K : ℝ)
    (ht : 0<t) (hh : t≤1) (hK : 1 ≤ K) (h : (∫ x,draught t⁻¹ x ∂G.probHaar) ≤ K*t^Δ) :
    (∫ U,ration I t U ∂prior G n) ≤ (K*t^Δ)^(rich n)*(t⁻¹^Δ)^I.card := by
  choose T hT using eliminates hn
  let d : Face (Per n) := (0,⟨(0,1),by decide⟩)
  let T' (i : E n) := if H : i∈paid n then T i H else d
  have he i (hi : i∈paid n) : i∈reads (T' i) ∧ ∀ u∈reads (T' i), u∈paid n → u≠i → index u < index i := by
    simpa only [T',dif_pos hi] using hT i hi
  have hj : Set.InjOn T' (paid n:Set (E n)) := by
    intro i hi k hk h; by_contra hh
    exact ((he i hi).2 _ (h.symm ▸ (he k hk).1) hk (Ne.symm hh)).not_gt
      ((he k hk).2 _ (h ▸ (he i hi).1) hi hh)
  let X := (paid n).filter fun i => T' i ∈ I
  let Y := (paid n).filter fun i => T' i ∉ I
  have hm : Y ⊆ paid n := filter_subset ..
  have hY : Y.image T' ⊆ Iᶜ := by
    intro j hi
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hi
    exact mem_compl.mpr (mem_filter.mp ha).2
  let f : G.El→ℝ := draught t⁻¹
  have hC : Continuous f := by unfold f draught; fun_prop
  have h0 (i : G.El) : 0 ≤ f i := (Real.exp_pos _).le
  have h₁ (i : G.El) : f i ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (G.chord_nonneg _))
  have hI : (∫ U,ration I t U ∂prior G n) ≤ (∫ i,f i ∂G.probHaar)^Y.card := by
    rw [← chosen_product hn f hC T' he Y hm]
    let g := fun U : Config G n=> ∏ i∈Y, f (faceValue U (T' i))
    have hg : Continuous g := continuous_finsetProd _ fun i _ => hC.comp (continuous_travel ..) -- name?
    refine integral_mono ((ration_cont ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun U => ?_)
    dsimp only [g]; let W := fun j => f (faceValue U j)
    change ∏ i∈Iᶜ,W i ≤ ∏ i∈Y,W (T' i)
    rw [← prod_image (g:=T') (by exact hj.mono hm),← prod_sdiff (f:=W) hY]
    refine mul_le_of_le_one_left (prod_nonneg fun i _=> h0 _) ?_
    exact le_trans (prod_le_prod (fun i _=>h0 (faceValue U _)) (g:=fun _ => 1) (fun i _=>h₁ _)) (by simp)
  have hZ : 0≤ ∫ i, f i ∂G.probHaar := integral_nonneg h0
  refine hI.trans ((pow_le_pow_left₀ hZ h Y.card).trans (per_hole _ _ _ _ _ _ hK ht hh ?_ ?_))
  · have he := rim_count hn; rw [howmany hn] at he; unfold rich
    have hg := Finset.card_le_card hm; omega
  have he := rim_count hn; rw [howmany hn] at he; unfold rich
  have hf : X.card+Y.card=(paid n).card := card_filter_add_card_filter_not ..
  have hx : X.card ≤ I.card := by
    have hX : X ⊆ paid n := filter_subset ..
    have hx : X.image T' ⊆ I := by
      intro i hi; obtain ⟨e,he,rfl⟩ := mem_image.mp hi; exact (mem_filter.mp he).2
    rw [← card_image_of_injOn (f:=T') (by exact hj.mono hX)]
    exact Finset.card_le_card hx
  omega

/-- Integrate one coordinate holding all others. Adapted here from
Torus.Integrals (which includes the private same trick for link fields).
Separable chart/station family not required. -/
private lemma shed_leaf {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι) (F H : (ι → G.El) → ℝ) (hF : Continuous F) (hH : Continuous H)
    (A : ℝ) (hh : ∀ z : ι → G.El, (∫ i, F (update z e i) ∂G.probHaar)=A)
    (h : ∀ (z : ι → G.El) (i : G.El), H (update z e i)=H z) :
    (∫ z,F z*H z ∂(Measure.pi fun _ => G.probHaar)) = A * ∫ z,H z ∂(Measure.pi fun _ => G.probHaar) := by
  --
  let p (i : ι) := i≠e
  let I := {i : ι // ¬p i}; let J := {i : ι // p i}
  let μ := Measure.pi fun _ : I => G.probHaar
  let ν := Measure.pi fun _ : J => G.probHaar
  let law := Measure.pi fun _ : ι => G.probHaar
  let W := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G.El) p
  let v : I := ⟨e,by simp [p]⟩
  let u (s : J → G.El) := W.symm (s,fun _=>1)
  have hM : MeasurePreserving W.symm (ν.prod μ) law :=
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => G.probHaar) p).symm _
  have he (f : (ι → G.El) → ℝ) (hf : Continuous f) :
      (∫ z,f z ∂law) = ∫ s,(∫ t, f (W.symm (s,t)) ∂μ) ∂ν := by
    have ht := hf.integrable_of_hasCompactSupport (μ:=law) (HasCompactSupport.of_compactSpace _)
    exact (hM.integral_comp W.symm.measurableEmbedding _).symm.trans
      (integral_prod _ (hM.integrable_comp_of_integrable ht))
  have hx s (t : I → G.El) : W.symm (s,t) = update (u s) e (t v) := by
    funext i; by_cases hk : i=e
    · subst i; rw [update_self]
      change (Equiv.piEquivPiSubtypeProd p (fun _ : ι => G.El)).symm (s,t) _=_
      rw [Equiv.piEquivPiSubtypeProd_symm_apply,dif_neg v.property]
    rw [update_of_ne hk]
    change (Equiv.piEquivPiSubtypeProd p (fun _ : ι=> G.El)).symm (s,t) _=(Equiv.piEquivPiSubtypeProd p (fun _ : ι => G.El)).symm _ i
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply,dif_pos (show p i from hk)]
  have hg s : (∫ t : I → G.El,F (W.symm (s,t)) ∂μ)=A := by
    simp_rw [hx s]
    let f i := F (update (u s) e i)
    have hf : Continuous f := hF.comp (by fun_prop : Continuous (update (u s) e))
    let eval := fun t : I → G.El => t v
    have hm : μ.map eval = G.probHaar := by
      unfold μ; change (Measure.pi _).map (@Function.eval I (fun _=> G.El) v)=_; rw [Measure.pi_map_eval]; simp
    have hr := integral_map (φ:=eval) (μ:=μ) (f:=f) (measurable_pi_apply v).aemeasurable hf.aestronglyMeasurable
    rw [hm] at hr; exact hr.symm.trans (hh _)
  change (∫ z,F z*H z ∂law) = A * ∫ z,H z ∂law
  rw [he (fun z=>F z*H z) (hF.mul hH),he H hH,← integral_const_mul]; apply integral_congr_ae
  filter_upwards with s
  have hp t : H (W.symm (s,t))=H (u s) := hx s t ▸ h _ _
  simp_rw [hp,integral_mul_const,hg]; dsimp only [μ]; simp

-- tree of COARSE site rotations; not an additional assertion on gauge of F.
local notation "oak" n => (Finset.univ.filter (Push.Corrected.Torus.Tree (n:=n)))
lemma oak_count (hn : 2≤n.val) : (oak n).card+1=Fintype.card (Site n) := by
  have hf := howmany hn
  have hh : (oak n).card + (Push.Corrected.Torus.free n).card = Fintype.card (Site n)*4 := by
    rw [show Fintype.card (Site n)*4 = Fintype.card (E n) by simp [E,Edge,Axis],← card_univ]
    exact Finset.card_filter_add_card_filter_not ..
  omega

/-- Eliminate in the rotations on output sites. Any missing bonds at literal
physical positions, no assumptions on whether twists close on plaquettes. -/
theorem refresh (hn : 2≤n.val) (V Q : Config G n) (f : G.El→ℝ) (hf : Continuous f)
    (s : Finset (Bond n)) (hs : s ⊆ oak n) :
    (∫ z,(∏ i∈s,f (V i*((Lattice.gauge z Q i)⁻¹))) ∂Measure.pi (fun _ : Site n => G.probHaar)) =
      (∫ i,f i ∂G.probHaar)^s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s.Nonempty
    · let d := fun i : Bond n => length (arrives i)
      obtain ⟨e,ht,hE⟩ := s.exists_max_image d he
      let t := s.erase e
      let j := arrives e
      have hTree b (h : b ∈ s) := (mem_filter.mp (hs h)).2
      have hx : j≠e.1 := by
        have he' := grows hn e.1 e.2 (hTree e ht).2
        intro hi; change length j=length e.1+1 at he'; rw [hi] at he'; omega
      let F := fun (i : Bond n) (r : Site n → G.El) => f (V i*((Lattice.gauge r Q i)⁻¹))
      have hF i : Continuous (F i) := by unfold F Lattice.gauge; fun_prop
      let H := fun z => ∏ i∈t, F i z
      simp_rw [← Finset.mul_prod_erase _ _ ht]
      change (∫ z,F e z*H z ∂Measure.pi _) = _
      let A := ∫ x,f x ∂G.probHaar
      have hj (z : Site n → G.El) : (∫ i,F e (update z j i)∂G.probHaar)=A := by
        have hp (i) : V e*((Lattice.gauge (update z j i) Q e)⁻¹) = V e*i*(z e.1 * Q e)⁻¹ := by
          unfold Lattice.gauge; change V e*((update z j i e.1*Q e*(update z j i j)⁻¹)⁻¹)=_
          rw [update_self,update_of_ne (Ne.symm hx)]; group
        unfold F; simp_rw [hp]
        let q := fun i : G.El => V e*i*(z e.1 * Q e)⁻¹
        have hq : MeasurePreserving q G.probHaar G.probHaar := G.preserve_two_sided ..
        have hh := integral_map (φ:=q) (μ:=G.probHaar) (f:=f) hq.aemeasurable hf.aestronglyMeasurable
        rw [hq.map_eq] at hh; exact hh.symm
      have hsep (z : Site n→G.El) (i : G.El) : H (update z j i)=H z := by
        apply prod_congr rfl
        intro b hb
        obtain ⟨h₁,h₂⟩ := mem_erase.mp hb
        have h3 : arrives b ≠ j := fun h=>h₁ (enters_once hn (hTree _ h₂) (hTree _ ht) h)
        have h4 : b.1≠j := by
          intro h
          have ha := hE _ h₂; have hf := grows hn b.1 b.2 (hTree _ h₂).2
          change length (arrives b) ≤ length j at ha
          rw [show b.1+step b.2=arrives b from rfl,h] at hf; omega
        unfold arrives at h3; unfold F Lattice.gauge; rw [update_of_ne h3,update_of_ne h4] -- defeq
      rw [shed_leaf j (F e) H (hF e) (continuous_finsetProd t (fun b _ => hF b)) A hj hsep]
      change A * (∫ z,(∏ i∈t,F i z) ∂Measure.pi _) = _
      unfold F
      rw [ih t (Finset.erase_ssubset ht) ((Finset.erase_subset ..).trans hs)]
      simp only [A,t,← pow_succ',Finset.card_erase_add_one ht]
    simp only [Finset.not_nonempty_iff_eq_empty] at he
    subst s; simp

def sill (B : Finset (Bond n)) (t : ℝ) (V Q : Config G n) :=
    ∏ i∈((oak n) \ B),draught t⁻¹ (V i*(Q i)⁻¹)

lemma sill_cont (B : Finset (Bond n)) (t : ℝ) : Continuous (fun p : Config G n × Config G n => sill B t p.1 p.2) := by
  unfold sill draught; fun_prop


lemma spill (hn : 2≤n.val) (V Q : Config G n) (B : Finset (Bond n)) {t K : ℝ}
    (ht : 0<t) (hh : t≤1) (hK : 1 ≤ K) (h : (∫ x,draught t⁻¹ x ∂G.probHaar) ≤ K*t^Δ) :
    (∫ z,sill B t V (gauge z Q) ∂Measure.pi (fun _ : Site n => G.probHaar)) ≤
      (K*t^Δ)^(Fintype.card (Site n)-1)*(t⁻¹^Δ)^B.card := by
  unfold sill
  rw [refresh hn _ _ _ (by unfold draught; fun_prop) _ sdiff_subset]
  let o := oak n
  have hx := oak_count hn
  change o.card+1=Fintype.card (Site n) at hx
  have hp : 0 ≤ (∫ x : G.El,draught t⁻¹ x ∂G.probHaar) := integral_nonneg fun _ => (Real.exp_pos _).le
  refine (pow_le_pow_left₀ hp h (o \ B).card).trans
    (per_hole _ _ _ _ _ _ hK ht hh ?_ ?_)
  · have he : (o \ B).card ≤ o.card := Finset.card_le_card sdiff_subset; omega
  have he : o.card ≤ (o \ B).card + B.card := by
    -- card sdiff + card inter
    have hh := Finset.card_sdiff_add_card_inter o B
    have hf : (o ∩ B).card ≤ B.card := Finset.card_le_card inter_subset_right
    omega
  omega

/-- At integrated output, no cycle constraints between default noise bonds
are needed (one fixed predictor for each k). Retained subset arbitrary. -/
lemma everyBond {n : Side} (s : Finset (Bond n)) (Q : Config G n) (f : G.El→ℝ) (hf : Continuous f) :
    (∫ V : Config G n,(∏ i∈s, f (V i*(Q i)⁻¹)) ∂prior G n)=(∫ a,f a ∂G.probHaar)^s.card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    let R (j : Bond n) (V : Config G n) := f (V j*(Q j)⁻¹)
    let H := fun V => ∏ j∈s,R j V
    let L := ∫ i,f i ∂G.probHaar
    have hu j : Continuous (R j) := by unfold R; fun_prop
    have hq (V : Config G n) : (∫ x,R i (update V i x) ∂G.probHaar)=L := by
      simp_rw [R,update_self]
      let p := fun a:G.El => a*(Q i)⁻¹
      have hp : MeasurePreserving p G.probHaar G.probHaar := measurePreserving_mul_right ..
      have he := integral_map (φ:=p) (μ:=G.probHaar) (f:=f) hp.aemeasurable hf.aestronglyMeasurable
      rw [hp.map_eq] at he; exact he.symm
    have he (V : Config G n) (x : G.El) : H (update V i x)=H V := by
      apply prod_congr rfl; intro j hj; unfold R; rw [update_of_ne (show j≠i from fun e=>hi (e ▸ hj))]
    simp_rw [Finset.prod_cons]
    change (∫ V,R i V*H V ∂Measure.pi _) = L^_
    rw [shed_leaf i (R i) H (hu i) (continuous_finsetProd s (fun j _ => hu j)) L hq he]
    rw [show (∫ V,H V ∂Measure.pi fun _ => G.probHaar)=_ from ih]
    change L*L^_=L^_; rw [card_cons,← pow_succ']

def gapper (B : Finset (Bond n)) (t : ℝ) (V Q : Config G n) := ∏ i∈Bᶜ,draught t⁻¹ (V i*(Q i)⁻¹)
lemma gapper_cont (B : Finset (Bond n)) (t : ℝ) : Continuous (fun p : Config G n × Config G n => gapper B t p.1 p.2) := by unfold gapper draught; fun_prop
lemma gapper_nonneg (B : Finset (Bond n)) (t : ℝ) (V Q : Config G n) : 0≤gapper B t V Q := by apply prod_nonneg; intro i _; exact (Real.exp_pos _).le
lemma drain (B : Finset (Bond n)) (Q : Config G n) {t K : ℝ} (ht : 0<t) (hh : t≤1) (hK : 1≤K)
    (h : (∫ x,draught t⁻¹ x ∂G.probHaar) ≤ K*t^Δ) :
    (∫ V,gapper B t V Q ∂prior G n) ≤ (K*t^Δ)^(Fintype.card (Bond n))*(t⁻¹^Δ)^B.card := by
  unfold gapper; rw [everyBond _ Q _ (by unfold draught; fun_prop)]
  have hp : 0 ≤ (∫ x : G.El,draught t⁻¹ x ∂G.probHaar) := integral_nonneg fun _ => (Real.exp_pos _).le
  refine (pow_le_pow_left₀ hp h Bᶜ.card).trans (per_hole _ _ _ _ _ _ hK ht hh (card_le_univ _) ?_)
  rw [card_compl]; exact Nat.le_of_eq (Nat.sub_add_cancel (card_le_univ _)).symm
lemma gap_sill (B : Finset (Bond n)) (t : ℝ) (ht : 0<t) (V Q : Config G n) : gapper B t V Q ≤ sill B t V Q := by
  unfold gapper sill
  have he : (oak n) \ B ⊆ Bᶜ := fun i hi=>mem_compl.mpr (mem_sdiff.mp hi).2
  rw [←prod_sdiff he]
  apply mul_le_of_le_one_left (prod_nonneg (fun i _ => (Real.exp_pos _).le)); apply le_trans (prod_le_prod _ (g:=fun _ => (1:ℝ)) _)
  · simp
  · exact fun i _=> (Real.exp_pos _).le
  exact fun i _=> Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by exact neg_nonpos.mpr (inv_pos.mpr ht).le) (G.chord_nonneg _))

end YM.Further.RootedInteractingRemainder
