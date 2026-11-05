import YM.FullVolume.Hits

/-! Actual replication root costs for our variants of primary cylinders.
Use every offset at a fixed scale using centered smaller-scale estimates;
price varies with the scale in these statements. Uniform also in the
period (ALL p). -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Cells
open Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {n : Side} {d : ℕ}
variable {F H:Trial C}

/-- Same stencil and at **every** sufficiently fine fixed centered scale
and cutoff beyond it (in the strong `mesh` sense: eventually in N for
all p). -/
def Affords (F : Trial C) (u : ℕ → Cutoffs → ℝ) :=
    Stencil F ∧ ∀ᶠ m in atTop, ∀ᶠ i in mesh, ∃ h : m ≤ i.1,
      Interior ((center C.S i.2 h 0).chamber 0) (F i.1 i.2 0) ∧
        (center C.S i.2 h 0).rootTest (C.beta i.1 i.2) (F i.1 i.2 0) ≤ u m i

def Owed (F : Trial C) (v : Cutoffs → ℝ) := Affords F (fun _=>v)

/-- Handy consequence when asking only for bounds. Actual UV-weighted costs
as needed in `Owed`. -/
def Funded (F : Trial C) := ∃ u : ℕ→ℝ, Affords F (fun k _=> u k)

lemma Stencil.at_origin (ht: Stencil F) (m : ℕ) : ∀ᶠ i in mesh, ∃ hn:m ≤ i.1,
    Interior ((center C.S i.2 hn 0).chamber 0) (F i.1 i.2 0):=by
  obtain ⟨X,hX⟩:=ht
  filter_upwards [hX,deepen.eventually (stencil_fit C.S m X)] with i hi ⟨hu,he⟩
  exact ⟨hu,(hi.fits 0).enlarges (he ..)⟩

namespace Affords
variable (h:C.Makes) {u v : ℕ → Cutoffs → ℝ}

include h in
lemma every (hp:Affords F u) (m J:ℕ) (hJ:0<J): ∃ k:ℕ,
    ∀ᶠ i in mesh, ∃ h : m ≤ i.1, ∀ T : Tiling (C.side i.1 i.2), T.side.val=Cells.span C.S h i.2 →
      ∀ x∈T.margin 0 (T.side.val/J), Interior (T.chamber 0) (F i.1 i.2 x) ∧ T.rootTest (C.beta i.1 i.2) (F i.1 i.2 x) ≤ u k i := by
  have hw : ∀ᶠ k in atTop, (3*J:ℕ)*C.S.a k ≤ C.S.a m := by
    have hx := (C.S.shrinks.const_mul ((3*J:ℕ):ℝ)).eventually (ge_mem_nhds
      (show (↑(3*J:ℕ):ℝ) * 0 < C.S.a m from (mul_zero _).trans_lt (C.S.a_pos _)))
    exact hx
  obtain ⟨k,hh,hy,hK⟩:= ((eventually_ge_atTop m).and (hw.and hp.2)).exists
  obtain ⟨X,hX⟩:=hp.1; refine ⟨k,?_⟩
  filter_upwards [hK,hX] with i hi ht
  obtain ⟨hn,ha,hb⟩ := hi; refine ⟨hh.trans hn,fun T he x hx=> ?_⟩
  let t:= Cells.span C.S hn i.2
  have hv : C.S.a i.1 * t=C.S.a k:= C.S.embeds_scale (C.S.toDepth hn i.2)
  have hE : C.S.a i.1 * T.side.val=C.S.a m:= he ▸ C.S.embeds_scale (C.S.toDepth (hh.trans hn) _)
  have hy' : 3*t ≤ T.side.val/J:= by
    apply (Nat.le_div_iff_mul_le hJ).2
    apply (Nat.cast_le (α:=ℝ)).1; apply le_of_mul_le_mul_left _ (C.S.a_pos i.1)
    change (3*J:ℕ)*C.S.a k ≤ C.S.a m at hy
    rw [hE]; rw [←hv] at hy
    push_cast at *; linarith only [hy]
  exact Push.RelayDifference.offset hn T _ _ (he.symm ▸ Around.inherits hh hn) ht.translates (seamless h ..) ha hb (Lease.fewer T 0 hy' hx)
lemma enlarged (hp:Affords F u) (h:∀ᶠ m in atTop, ∀ᶠ i in mesh, u m i ≤ v m i): Affords F v:=
    ⟨hp.1,(h.and hp.2).mono fun _ hi=> (hi.1.and hi.2).mono fun _ hj=>⟨hj.2.choose,hj.2.choose_spec.1,hj.2.choose_spec.2.trans hj.1⟩⟩
include h in
lemma sub (hp:Affords F u) (hq:Affords H v):Affords (F-H) (u+v):=by
  refine ⟨hp.1.sub hq.1,?_⟩
  filter_upwards [hp.2,hq.2] with m hm ht
  filter_upwards [hm,ht] with i hi hv
  obtain ⟨hn,hF,hT⟩:=hi; obtain ⟨hi,hH,hY⟩:=hv
  have he:= hH.scale (-1:ℂ)
  let X:= center C.S i.2 hn 0; let β:= C.beta i.1 i.2
  let z:= F i.1 i.2 0; let w:= H i.1 i.2 0
  have hW:Interior (X.chamber 0) (-w):= by
    rw [← neg_one_smul ℂ w]; exact he
  refine ⟨hn,?_,?_⟩
  · change Interior _ (z-w); rw [sub_eq_add_neg]; exact hF.plus hW
  change X.rootTest β (z-w) ≤ u m i+v m i
  rw [sub_eq_add_neg]
  apply ((seamless h ..).semi X z (-w) hF hW).trans (add_le_add hT ?_)
  rw [← neg_one_smul ℂ w,Next.Extract.root_smul]; simpa
lemma scalar (hp: Affords F u) (a:Cutoffs→ℂ): Affords (fun N p x=> a (N,p) • F N p x) (fun k i=> ‖a i‖ * u k i):=by
  obtain ⟨⟨X,hX⟩,ht⟩:=hp
  refine ⟨⟨X,hX.mono fun i hi=> hi.smul (a i)⟩,?_⟩
  filter_upwards [ht] with k hk
  filter_upwards [hk] with i hi
  obtain ⟨h,hF,hK⟩:=hi
  refine ⟨h,hF.scale _,?_⟩
  rw [Next.Extract.root_smul]; exact mul_le_mul_of_nonneg_left hK (norm_nonneg _)
lemma neg (hp: Affords F u): Affords (-F) u:=by
  simpa only [neg_one_smul, norm_neg,norm_one,one_mul] using! (hp.scalar (fun _=>(-1:ℂ)))
include h in
lemma add (hp:Affords F u) (hq:Affords H v):Affords (F+H) (u+v):=by
  rw [← sub_neg_eq_add]; exact sub h hp hq.neg
lemma zero : Affords (0:Trial C) 0:=by
  have hu(n:Side)(X:Tiling n)(β:ℝ): X.rootTest β (fun _ : Config G n=> (0:ℂ))=0:= by simpa using! Next.Extract.root_smul X β (0: Config G n → ℂ) 0
  have hz (N p:ℕ):Push.RelayDifference.Local ∅ (fun (_: Site (C.side N p)) (_:Config G (C.side N p))=> (0:ℂ)):= ⟨fun _ _=>rfl,fun _=>Interior.constant _ _⟩
  refine ⟨⟨∅,Eventually.of_forall (fun i=> hz i.1 i.2)⟩,Eventually.of_forall (fun m=> ?_)⟩
  filter_upwards [deepen.eventually_ge_atTop m] with i hi using
    ⟨hi, Interior.constant _ _, (hu (C.side i.1 i.2) _ _).le⟩
include h in
lemma sum {ι} (s : Finset ι) (F : ι→Trial C) (u : ι→ℕ→Cutoffs→ℝ) (hp : ∀ i∈s, Affords (F i) (u i)) :
    Affords (∑ i∈s,F i) (∑ i∈s,u i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact zero
  | insert a s ha ih=> simp only [Finset.sum_insert ha]; exact add h (hp _ (Finset.mem_insert_self ..)) (ih (fun i hi=>hp _ (Finset.mem_insert_of_mem hi)))

lemma recurses (h : Affords F u) (hp : ∀ᶠ i in mesh,F i.1 i.2=H i.1 i.2): Affords H u:=by
  obtain ⟨⟨X,hX⟩,he⟩:=h
  refine ⟨⟨_,(hX.and hp).mono fun i hi=> hi.2 ▸ hi.1⟩,he.mono fun i hi=>?_⟩
  filter_upwards [hp,hi] with j hv hh; rw [← hv]; exact hh
end Affords
namespace Funded
variable (h:C.Makes)
lemma neg (hp:Funded F) : Funded (- F):=by
  obtain ⟨u,hp⟩:=hp; exact ⟨u,hp.neg⟩
include h in
lemma sub (hp:Funded F) (hq:Funded H):Funded (F-H):=by
  obtain ⟨u,hp⟩:=hp; obtain ⟨v,hq⟩:=hq; exact ⟨u+v,Affords.sub h hp hq⟩
include h in
lemma primaries (hC:Extraction.Wcmain C) (v : Bid.Rowe C d) {Y:ℝ} (he:∀ᶠ i in mesh, ‖v i‖ ≤ Y) : Funded (Bid.upper C v):=by
  let X:= max 1 Y
  obtain ⟨A,hA,hP⟩:=hC d X 1 (zero_lt_one.trans_le (le_max_left ..)) (by norm_num)
  let a m:= A * C.S.a m ^ (-(d:ℝ)-1)
  refine ⟨a,(Stencil.visits h v),?_⟩
  filter_upwards [eventually_ge_atTop (C.ref d)] with i hi
  filter_upwards [deepen.eventually (hP i hi),he] with j hj ht
  obtain ⟨hn,hD,hF⟩:= hj j.2 (v j) (ht.trans (le_max_right ..))
  exact ⟨hn,hF 0⟩
end Funded
end YM.FullVolume
