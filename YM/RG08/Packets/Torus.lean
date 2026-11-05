import YM.RG08.Packets.Swing

/-!
# Taking a cover packet through a coarse translation-invariant mesh column (exact periodization)
-/
noncomputable section
namespace YM.RG08.Packets
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix
open scoped Topology ENNReal

set_option autoImplicit false
variable {α β γ : Type} {L L' : Side} {c f : Side}

def pass {α : Type} (u : Cover) (x : Market α) : Market α := (x.1+u,x.2)

def city (L : Side) (T : Kernel α β) := ∀ x y u, T (pass (L.val • u) x) (pass u y)=T x y

def town (L : Side) (T : Packet 1 α) := city L (fun x y=>T x (fun _=>y)) -- used L=1 only

theorem pass_one (R : Row α β) : city 1 (plain R) := by
  intro x y u
  change R x.2 y.2 (_+_-(_+_))=R x.2 y.2 (y.1-x.1)
  rw [show (1:Side).val=1 from rfl,one_smul]; congr 1; abel

theorem pass_here (T : Cross L α β) : city L (install T) := by
  intro x y u
  obtain ⟨hk,hq⟩:=rent_raw (rent L x.1+u) _ (wrap L x.1) (show x.1+L.val • u=lift (wrap L x.1)+L.val • (rent L x.1+u) by rw [smul_add,←add_assoc, ← rent_balance L x.1])
  unfold pass install
  rw [show (x.1+_,x.2).1=x.1+L.val • u from rfl,hq,hk]
  congr 1; change (y.1+u)-(_+u)=_; abel

theorem pass_bind [Fintype β] {T : Kernel α β} {B : Kernel β γ} (h : city L T) (ht : city L' B) : city (L*L') (bind T B) := by
  intro x y u
  rw [bind_apply,bind_apply]; refine Finset.sum_congr rfl fun i _=> ?_
  unfold tagged
  let E : Cover≃Cover:=Equiv.addRight (L'.val • u)
  rw [← E.tsum_eq]; apply tsum_congr; intro b
  change T _ (pass (L'.val • u) (b,i)) * B (pass (L'.val • u) (b,i)) _ = _
  rw [ht,← h x (b,i) (L'.val • u)]
  congr 3
  exact (mul_smul L.val L'.val u) -- location goal?

theorem pass_response (V : Precision.Towers L)(H K : Precision.Bed) : city L (response V H K) := by
  simpa only [response,sandwich,one_mul,mul_one] using
    pass_bind (pass_bind (pass_one H.inverse) (pass_here V.T)) (pass_one K.metric)

def Loop (c : Side) (y : Site c) := {z : Cover | wrap c z=y}

private theorem around (m : Side) (z : Cover) : m.val • wrap m z=0 := by funext i; rw [Pi.smul_apply,nsmul_eq_mul]; simp [Per]

def roads (c : Side) (y : Site c) : Cover ≃ ↥(Loop c y) where
  toFun z := ⟨lift y+c.val • z,by unfold Loop; rw [Set.mem_setOf_eq,map_add,map_nsmul,wrap_lift,around,add_zero]⟩
  invFun z := rent c z.1
  left_inv z := (rent_raw z _ _ (by rfl)).2
  right_inv z := Subtype.ext (by
    have h := z.property
    change wrap c z.val=y at h
    change lift y+c.val • rent c z.val=z.val
    conv_lhs => lhs; rw [← h]
    exact (rent_balance c z.val).symm)

/-- Periodic matrix evaluation resolved into explicit lifted paths. -/
theorem circuit (c : Side) (K : Kernel α β) (x : Market α) (y : Co c β) :
    display K c x y = ∑' v:Cover,K x (lift y.1+c.val • v,y.2) := by
  classical
  let s := Loop c y.1
  let f (z:Cover) := K x (z,y.2)
  have h : display K c x y=∑' z, s.indicator f z := tsum_congr fun z=>by
    unfold s Loop f Set.indicator
    simp only [Set.mem_setOf_eq]
  rw [h,← tsum_subtype s f, ← (roads c y.1).tsum_eq]
  rfl

/-- Transpose of a periodic matrix is exactly displayed by the opposite orientation of its
cover kernel. Keep the translations by whole *fine* periods vs *coarse* periods linked.
-/
theorem matches_back {T : Kernel α β} {M : Matrix (Co f α) (Co c β) ℝ} (hc : f.val=c.val*L.val) (h : city L T) (ht : Matches T M) : Matches (swap T) M.transpose := by
  intro x y
  have he : x=pass (c.val • rent c x.1) (lift (wrap c x.1),x.2) := Prod.ext (rent_balance c x.1) rfl
  let H : Cover ≃ Cover := (Equiv.neg _).trans (Equiv.addRight (rent c x.1))
  change display (swap T) f x y=M y (wrap c x.1,x.2)
  rw [circuit,← show (wrap f (lift y.1),y.2)=y from Prod.ext (wrap_lift _) rfl,← ht (lift y.1,y.2), circuit]
  rw [← H.tsum_eq]
  refine tsum_congr fun v=> ?_
  have hZ : pass (-(c.val • (H v))) x = (lift (wrap c x.1)+c.val • v,x.2) := by
    ext1
    · rw [he]; change lift _ + _ + _ = _
      -- he also changed RHS. reduce instead separately
      simp only [pass] at *
      simp only [map_add,map_nsmul,wrap_lift,around,add_zero] -- goal may different
      change lift _ + c.val • rent c x.1 + -(c.val • (-v+rent c x.1)) = lift _ + c.val • v
      rw [smul_add,smul_neg]; abel
    rfl
  have hY : pass (L.val • (-(c.val • H v))) (lift y.1+f.val • H v,y.2) = ((lift y.1,y.2):Market α) := by
    unfold pass; congr 1
    simp_rw [smul_neg,← mul_smul, hc,mul_comm L.val c.val]; abel
  have hp := h (lift y.1+f.val • H v,y.2) x (-(c.val • H v))
  dsimp [swap]
  rw [wrap_lift,← hp,hZ,hY]
  -- rhs after rw circuit includes lift (wrap...) etc y's

end YM.RG08.Packets
