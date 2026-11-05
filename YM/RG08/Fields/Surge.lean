import YM.RG08.Fields.Allure
import YM.RG08.Crossing.Flats

/-!
# kbulk version. Even if using the unmodified metric, the allocated
costs can be announced pre-L, not patch hitting, with post-index _. Curve
here denotes a single line of the full propagator, different from CoveCov.
Don't expense either absolute path derivatives on a real density or UV-real
column stability from these. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Wings
open scoped Topology BigOperators
variable {G : Gauge}

structure Quilt (k : ℝ) (b : ℕ→ℝ) where
  width : ℕ→ℝ
  alpha : ℕ→ℕ→ℝ
  wp i : 0<width i
  ap i j : 0<alpha i j
  C : ℕ→ℝ
  solvent i : 0≤C i
  bed : ∀ j, 4 ≤ j → Frost k j (b j) (width j) (C j)
  post : (i j:ℕ) → Flight i j → ℝ
  upright i j S : 0≤post i j S
  uprights i j (S : Flight i j) : 4≤j → Stairs S k (b i) (b j) (alpha i j) (post i j S)
  fee : ℕ→ℝ
  nonneg i : 0≤fee i
  line i (hx:4 ≤ i) : ∀ (v:Train i) (a b : TypeFace 1) x,‖olog k v a b x‖≤ fee i
  rises i : 4 ≤ i → ∀ (v w:Train i) X, 0≤X → (minusRows (hessian (pink k v)) (hessian (pink k w))).strip (b i) X →
    ∀ (a b:TypeFace 1) x,‖olog k v a b x- olog k w a b x‖≤ fee i * X

lemma entrance {k : ℝ} (hk : 0 < k) {b : ℕ→ℝ} (hb : ∀ i,0<b i) : Nonempty (Quilt k b) := by
  have he i : ∃ s C : ℝ, 0<s ∧ 0 ≤ C ∧ (4 ≤ i → Frost k i (b i) s C) := by
    by_cases hi : 4 ≤ i
    · obtain ⟨q,B,hq,hB,H⟩:= possible_frost hk hi (hb i); exact ⟨q,B,hq,hB,fun _=>H⟩
    exact ⟨1,1,one_pos,zero_le_one,fun h=>(hi h).elim⟩
  have hx (i j:ℕ) : ∃ α>0, ∀ (S : Flight i j),∃ C:ℝ, 0≤C ∧ (4≤j → Stairs S k (b i) (b j) α C) := by
    by_cases ht:4≤j
    swap
    · exact ⟨1,one_pos,fun S=>⟨1,zero_le_one,fun h=>(ht h).elim⟩⟩
    by_cases hi:4 ≤ i
    swap
    · exact ⟨1,one_pos,fun S=>(hi S.legal).elim⟩
    obtain ⟨a,ha,H⟩:= before_S hk hi ht (hb i) (hb j); refine ⟨a,ha,fun S=>?_⟩; obtain ⟨C,hC,H⟩:=H S; exact ⟨C,hC.le,fun _=> H⟩
  have hh (j:ℕ) : ∃ C:ℝ,0≤C ∧ (4≤j → ∀ (v : Train j) (a b:TypeFace 1) x, ‖olog k v a b x‖≤ C) ∧
      (4≤j → ∀ (v w : Train j) X, 0 ≤ X → (minusRows (hessian (pink k v)) (hessian (pink k w))).strip (b j) X →
      ∀ (a c:TypeFace 1) x, ‖olog k v a c x - olog k w a c x‖≤ C*X) := by
    by_cases h : 4≤ j
    · obtain ⟨C,hc,H⟩:=poet_kern hk h; obtain ⟨D,hd,F⟩:=poet_varies hk h (hb j)
      exact ⟨max C D,hc.trans (le_max_left ..),fun _ v a b x=> (H v a b x).1.trans (le_max_left ..),
         fun _ v w X hX hu a b i=> (F v w X hX hu a b i).1.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hX)⟩
    exact ⟨0,le_rfl,fun ht=>(h ht).elim,fun ht=>(h ht).elim⟩
  choose w B hw hB hW using he
  choose a ha Z using hx; choose P hP hp using fun i j=> Z i j
  choose F hF H hH using hh
  exact ⟨⟨w,a,hw,ha,B,hB,hW,P,hP,hp,F,hF,H,hH⟩⟩

variable {X : Chain} {b:ℕ→ℝ} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} {S : Prism G X.kernel g P E} {ν : G.ColorIndex} {D : ChartRatio G}
variable {I : Type} {u : I→Windows}
structure Plays (u:I→Windows) (Q : Quilt X.kernel.penalty b) : Prop where
  hearth : Weighed (Launch.farY X) (fun i:Launch u=> Q.C (X.J i.i))
  rise : Weighed (Launch.farY X) (fun i:Launch u=> Q.post _ _ (X.step i.i (.top _)))
  full : Weighed (Launch.farY X) (fun i:Launch u=> Q.fee (X.J i.i))
variable {Q : Quilt X.kernel.penalty g.w}
abbrev glance (X : Chain) (N i : ℕ) : Row (TypeFace 1) (TypeFace 1):=olog X.kernel.penalty (X.history N i)

lemma harvest (h : Circuit S ν D u) (hx : Plays (X:=X) u Q) : ∃ R D : Wings u 0→ℝ, Weighed (Wings.menu X) R ∧
    Weighed (Wings.menu X) D ∧ ∀ i,
      let s:=Q.width (X.J i.i); let k:=X.kernel.penalty; let v:=X.history i.N i.i; let w:=X.history i.M i.i; let W:= R i*Wings.chop X (1/4) i
      Chords (R i) W (pink k v) (pink k w) s ∧ Chords (R i) W (blue k v) (blue k w) s ∧ ∀ a b x,
      ‖glance X i.N i.i a b x‖≤D i ∧ ‖glance X i.M i.i a b x‖≤D i ∧ ‖glance X i.N i.i a b x-glance X i.M i.i a b x‖≤D i*chop X (1/4) i := by
  obtain ⟨B,hB,H⟩:= Wings.mail h
  let C (i : Wings u 0):=Q.C (X.J i.i); let F (i : Wings u 0):= Q.fee (X.J i.i)
  have hu:Weighed (menu X) C := hx.hearth.transfer toLaunch; have hv:Weighed (menu X) F:=hx.full.transfer toLaunch
  let Y:= (1:Wings u 0→ℝ)+B; have hY : Weighed (menu X) Y:= (Weighed.one).plus hB (sh _)
  refine ⟨_,_,hu.times hY,hv.times hY,fun i=>?_⟩
  intro s k v w W
  let A:= chop X (1/4) i
  have he : 0<A:= gain_pos ..
  have hg:B i≤ Y i:= le_add_of_nonneg_left zero_le_one
  have hR:1 ≤ Y i:=le_add_of_nonneg_right (hB.positive i)
  have ht : 0≤B i*A := mul_nonneg (hB.positive i) he.le
  have hp := Q.bed (X.J i.i) (X.adm _)
  have hm := hp.lift _ v w ht (H i)
  have ha : B i*A*C i ≤ C i * Y i * A := le_trans (le_of_eq (by ring : _=C i*B i * A)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (hu.positive i)) he.le)
  refine ⟨⟨strip_mono (hp.hue v).1 le_rfl (le_mul_of_one_le_right (hu.positive i) hR),strip_mono (hp.hue w).1 le_rfl (le_mul_of_one_le_right (hu.positive i) hR),strip_mono hm.1 le_rfl ha⟩,
       ⟨strip_mono (hp.hue v).2 le_rfl (le_mul_of_one_le_right (hu.positive i) hR),strip_mono (hp.hue w).2 le_rfl (le_mul_of_one_le_right (hu.positive i) hR),strip_mono hm.2 le_rfl ha⟩,fun a b t=>?_⟩
  have hc := Q.line _ (X.adm i.i)
  refine ⟨(hc v a b t).trans (le_mul_of_one_le_right (hv.positive i) hR),(hc w a b t).trans (le_mul_of_one_le_right (hv.positive i) hR),?_⟩
  exact (Q.rises _ (X.adm i.i) _ _ _ ht (H i) a b t).trans (by rw [Pi.mul_apply,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg he.le) (hv.positive i))
private lemma r_stage (h:Circuit S ν D u) : ∃ R:Wings u 1→ℝ, Weighed (menu X) R ∧ ∀ i,
    let s:=R i*chop X (1/104) i
    (minusRows (X.K₀ i.N i.up.i) (X.K₀ i.M i.up.i)).strip (g.w (X.J i.up.i)) (s^26) ∧
    (minusRows (X.K₀ i.N i.i) (X.K₀ i.M i.i)).strip (g.w (X.J i.i)) (s^26) ∧ 1 ≤ R i := by
  obtain ⟨C,hC,H⟩ := mail h
  let a (i: Wings u 1):= C i.up; let b (i: Wings u 1):= C i.low; let L (i : Wings u 1) := ((X.S.block i.i).val:ℝ)
  have hu : Weighed (menu X) a := (aged_up X h.M.crop).sway (sh X) (hC.transfer up); have hv:Weighed (menu X) b:=hC.transfer low; have ht : Weighed (menu X) L := h.M.crop.transfer toLaunch
  let A:=a*L; let r:=1+(A+b)
  have hA : Weighed (menu X) A:= hu.times ht
  refine ⟨r,(Weighed.one).plus (hA.plus hv (sh X)) (sh X),fun i=>?_⟩
  have he : 1≤r i:=le_add_of_nonneg_right (add_nonneg (hA.positive i) (hv.positive i))
  have hy : r i ≤ r i^26 := by simpa only [pow_one] using pow_le_pow_right₀ he (by decide : 1≤ (26:ℕ))
  have hz : A i+b i ≤ r i := le_add_of_nonneg_left zero_le_one
  have hm : chop X (1/104) i ^26=chop X (1/4) i := by unfold chop gain; rw [← Real.exp_nat_mul]; congr 1; ring
  intro s
  have hh : 0<chop X (1/4) i:= gain_pos ..
  refine ⟨strip_mono (H i.up) le_rfl ?_,strip_mono (H i.low) le_rfl ?_,he⟩
  · unfold s; rw [mul_pow,hm]; calc
      _ ≤ A i*chop X (1/4) i:= by rw [show A i*chop X (1/4) i = a i*(L i*chop X (1/4) i) from mul_assoc ..]; exact mul_le_mul_of_nonneg_left (continued' X _ (by norm_num) i) (hu.positive i)
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right (hv.positive i)).trans (hz.trans hy)) hh.le
  unfold s; rw [mul_pow,hm]; exact mul_le_mul_of_nonneg_right (show b i≤ _ from (le_add_of_nonneg_left (hA.positive i)).trans (hz.trans hy)) hh.le
lemma minor_rails (h : Circuit S ν D u) (hx : Plays (X:=X) u Q) : ∃ C : Wings u 1 → ℝ, Weighed (menu X) C ∧ ∀ i,
    let k:= X.kernel.penalty; let α:=Q.alpha (X.J i.up.i) (X.J i.i); let P:= X.flight i.N i.i; let R:=X.flight i.M i.i
    let A:= C i*chop X (1/104) i
    Chords (ι:=Co (X.S.block i.i) (TypeFace 1)) (C i) A (X.A₀ i.N i.i) (X.A₀ i.M i.i) α ∧ Chords (C i) A (P.duo k).T (R.duo k).T α ∧ Chords (C i) A (P.psi k) (R.psi k) α := by
  obtain ⟨A,hA,H⟩:=r_stage h
  have hv:=hx.rise.transfer (toLaunch (u:=u) (k:=1))
  refine ⟨_,hv.times hA,fun i=>?_⟩
  let P:= X.history i.N (i.i+1); let R:=X.history i.M (i.i+1)
  let U:=X.step i.i (.top _)
  have hs:=Q.uprights _ _ U (X.adm _)
  let l:=A i*chop X (1/104) i
  have hu := hs.up l P R (mul_nonneg (hA.positive i) (gain_pos ..).le) (H i).1
  have hh: X.K₀ i.N i.i=hessian (pink X.kernel.penalty (flutter U P).land) := by
     unfold Chain.K₀ Chain.metric; rw [X.history_step _ _ i.cut]; rfl
  have hh': X.K₀ i.M i.i=hessian (pink X.kernel.penalty (flutter U R).land):= by
     unfold Chain.K₀ Chain.metric; rw [X.history_step _ _ (i.cut.trans i.side)]; rfl
  have hg : (minusRows _ _).strip (g.w (X.J i.i)) (l^26) := (H i).2.1
  rw [hh,hh'] at hg
  have hk:=hu hg
  have hL:= le_mul_of_one_le_right (hv.positive i) (H i).2.2
  refine ⟨hk.1.tack le_rfl hL (le_of_eq (mul_assoc ..).symm),hk.2.1.tack le_rfl hL (le_of_eq (mul_assoc ..).symm),hk.2.2.tack le_rfl hL (le_of_eq (mul_assoc ..).symm)⟩
end YM.RG08.Drift
