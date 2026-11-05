import YM.Contacts.Layers.Ahead

/-! # Matching within a T-layer

Use the one-scale OPE to **arbitrarily large output horizon**, as needed by the geometry
after any further filter refinement. It controls all the reader placements used here, not
just a reader with fixed bounds on its clearance from the cluster. Testing exteriors at unit
(rough) layer in `Precision` does NOT mean paying this exponent in the final estimates.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set MeasureTheory Table Spec OPE
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {I J W : Type} [Fintype I] [Fintype J]
variable {F : Extraction.Order} {Z : Final C F S} {M : Devices Z.sector.derivatives}
variable {φ : Filter W} {T : W → ℝ} {c d r s u v : ℝ}
variable {x : W → E4} {A B : Set (W → E4)}
variable {X : W→ I→E4} {Y : W→ J→ E4}
local notation "D" => M.basis
local notation "TK" => C.book.Token
local notation "EP" => W → Expression Z.sector.derivatives
variable {e f : W → Expression Z.sector.derivatives}

inductive Override (Z : Final C F S) (M : Devices Z.sector.derivatives) (φ : Filter W) (T : W→ℝ)
    (x : W → E4) (s c : ℝ) : (W → Expression Z.sector.derivatives) → Prop
| atom {d : ℕ} {f : W → S.Field d} (h : RateLE φ T f (c-d*s)) : Override Z M φ T x s c
    (fun i=> insertField M.basis (x i) d (f i))
| zero : Override Z M φ T x s c 0
| plus {e f : W → Expression Z.sector.derivatives} : Override Z M φ T x s c e → Override Z M φ T x s c f → Override Z M φ T x s c (e+f)
| germ {e f : W → Expression Z.sector.derivatives} : Override Z M φ T x s c e → e =ᶠ[φ] f → Override Z M φ T x s c f
namespace Override
omit [Fintype I] in
lemma sum {p : Finset I}{E : I→W→ Expression Z.sector.derivatives} (h : ∀ i∈p,Override Z M φ T x s c (E i)) :
    Override Z M φ T x s c (∑ i∈p, E i) := by
   induction p using Finset.induction_on with
   | empty => rw [Finset.sum_empty]; exact .zero
   | insert i p hi ih => rw [Finset.sum_insert hi]; exact (h i (by simp)).plus (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma mono (h : Override Z M φ T x s c e) (hu : u ≤ s) (hd : c ≤ d) : Override Z M φ T x u d e:= by
   induction h with
   | @atom a f h => exact .atom (h.mono (by gcongr))
   | zero => exact .zero
   | plus _ _ hx hy => exact hx.plus hy
   | germ _ h hx=> exact hx.germ h
lemma coeff (h : Override Z M φ T x s c e) {g : W → ℂ} (hf : RateLE φ T g d) : Override Z M φ T x s (d+c) (fun i=>g i • e i) := by
   induction h with
   | @atom a f h => exact (.atom ((hf.smul h).mono (le_of_eq ((add_sub_assoc ..).symm))) : Override Z M φ T x s (d+c) _).germ (Eventually.of_forall fun i=> map_smul (insertField D (x i) a) (g i) (f i))
   | zero => simp only [Pi.zero_apply,smul_zero]; exact .zero
   | @plus e f _ _ hx hy => exact (hx.plus hy).germ (Eventually.of_forall fun i=> (smul_add (g i) (e i) (f i)).symm)
   | germ _ h hx=> exact hx.germ (h.mono fun i hi=> congr_arg (g i • ·) hi)
variable (hT : Tendsto T φ atTop)
include hT
lemma fine (h : Override Z M φ T x s c e) (hx : x∈ A) : Fine M φ T A s c e := by
   induction h with
   | atom h=> exact Fine.field hT hx h
   | zero => exact .zero
   | plus _ _ hx hy=> exact hx.plus hy
   | germ _ h hx=> exact hx.germ h
-- everything in e.g. a projected output through the horizon has weight ≤ its horizon.
lemma row (h : Override Z M φ T x s c e)(hs : 0 ≤ s) (w : ℕ) : RateLE φ T (fun i=> M.row (x i) w (e i)) (c - w*s) := by
   induction h with
   | @atom d f h =>
     by_cases he:w ≤ d
     · simp_rw [M.row_of_field]; exact (rate_linear (LinearMap.toContinuousLinearMap (M.splitting.part w d)) hT h).mono (by gcongr)
     simp_rw [M.row_of_field, M.splitting.beyondZero (show d<w from not_le.mp he), LinearMap.zero_apply]; exact RateLE.zero φ T (X:=S.Field w) _
   | zero => simp only [Pi.zero_apply,map_zero]; exact RateLE.zero φ T (X:=S.Field w) _
   | plus _ _ hx hy=> simp_rw [Pi.add_apply,map_add]; exact hx.add hy hT
   | germ _ h hx=> exact hx.congr (h.mono fun i hi=> congr_arg (M.row (x i) w) hi)
lemma residue (h : Override Z M φ T x s c e)(hs : 0 ≤ u)(hu : u ≤ s) (w : ℕ) (hx : x∈A) : Fine M φ T A u
      (c - (w+1:ℝ)*(s-u)) (fun i=> M.residue (x i) w (e i)):= by
   induction h with
   | @atom d f h =>
     by_cases he : d ≤ w
     · simp_rw [M.residue_low _ he]; exact .zero
     -- every output of grade ≤w paid with price of same term of grade d
     have he' : (w:ℝ)+1 ≤ d := by exact_mod_cast (Nat.add_one_le_of_lt (not_le.mp he))
     have hl : c-(d:ℝ)*s ≤ c-(w+1:ℝ)*(s-u)-d*u:= by linarith only [mul_le_mul_of_nonneg_right he' (sub_nonneg.mpr hu)]
     let g(i):= M.project (x i) w (insertField D (x i) d (f i)); have hf : RateLE φ T g (c-(d:ℝ)*s):= by
        unfold g; simp_rw [← M.project_through,M.row_of_field]; refine RateLE.sum hT fun j _=>?_
        exact rate_linear (LinearMap.toContinuousLinearMap (Z.sector.derivatives.rise (show j.val ≤ w from Nat.le_of_lt_succ j.isLt))) hT (rate_linear (LinearMap.toContinuousLinearMap (M.splitting.part j d)) hT h)
     have hX:= Fine.field (M:=M) hT hx (hp:=h.mono hl)
     exact hX.diff (Fine.field hT hx (hf.mono (hl.trans (by gcongr; omega))))
   | zero=> simp only [Pi.zero_apply,map_zero]; exact .zero
   | plus _ _ hx hy=> simp_rw [Pi.add_apply,map_add]; exact hx.plus hy
   | germ _ h hx=> exact hx.germ (h.mono fun i hi=> congr_arg (M.residue (x i) w) hi)
end Override

-- Envelope condition at the current T-layer. No need that every detail of the cluster be in it, only the palette.
def Habitat (φ : Filter W) (T : W→ℝ) (s : ℝ) (x : W → E4) (A : Set (W → E4)) := ∀ y ∈ A, RateLE φ T (fun i => y i-x i) (-s)
lemma habitat_gives (hh : Habitat φ T s x A) (h : carries A X) : enveloped φ T s X x := by
  intro b hb; filter_upwards [eventually_all.mpr fun i=> hh _ (h i) b hb] with i hi using (pi_norm_le_iff_of_nonneg (Real.exp_nonneg (b*T i))).mpr hi

structure Matchable (Z : Final C F S) (M : Devices Z.sector.derivatives) (φ : Filter W) (T : W→ℝ) (A : Set (W → E4)) (x : W → E4) (s u c : ℝ) (e : W → Expression Z.sector.derivatives) : Prop where
   replaces (q : ℝ) : ∃ z, Override Z M φ T x s c z ∧ Precision Z M φ T A u q (e-z)
namespace Matchable
variable [hnb : φ.NeBot] (hT : Tendsto T φ atTop) (H : Services C F S)
variable (p : I → C.book.Token) (ha : Habitat φ T s x A) (hs : u < s) (hu : 0 ≤ u) (hv : s ≤ 1)
variable (hx : x∈ A) (hk : Kept φ T s X)(hU : carries A X)

-- for approximants only; not a new prescription changing fields or truncations each use
omit hnb
def internal (x : I→ E4) (p : I→ C.book.Token) (t : E4) (M : Devices Z.sector.derivatives) (n : ℕ) : Expression Z.sector.derivatives := ∑ i∈bands Z.sector.derivatives n, M.basis.ope i x p t • insertToken M.basis t (M.basis.letter i)
include hT ha hs hu H hx hk hv hU
include hnb -- invalid syntax?
lemma from_word : Matchable Z M φ T A x s u ((sigma p:ℝ)*s) (fun t=> tokenWord M.basis (X t) p) := by
  have hx' := habitat_gives ha hU; have hs' := lt_of_le_of_lt hu hs
  refine ⟨fun r=>?_⟩; obtain ⟨n,hn⟩:= exists_nat_gt (((sigma p:ℝ)*s-r)/(s-u)); let E(t):= internal (X t) p (x t) M n
  refine ⟨E,(Override.sum (p:=bands Z.sector.derivatives n) (E:= fun j t=> M.basis.ope j (X t) p (x t) • insertToken D (x t) (M.basis.letter j)) (fun i hi=> ?_)).germ (Eventually.of_forall fun i=> Finset.sum_apply ..),?_⟩
  · have h: Override Z M φ T x s (i.1*s) (fun t=>insertToken D (x t) (M.basis.letter i)):= by
       unfold insertToken; refine .atom (RateLE.mono (RateLE.const (S.project i.1 (M.basis.letter i).2) hT) (by change 0 ≤ (i.1:ℝ)*s-i.1*s; linarith only))
    exact Override.mono (h.coeff (available_cost Z D p hT H M.coherent hx' hk hs' i)) le_rfl (by apply le_of_eq; ring)
  refine Against.of_words hT (fun J _ Y q hh he l=>?_)
  have hs:= he.windows hU pack_carries; have hf:= he.left hx pack_carries
  -- read the signed approximation before taking the bound; every allowed exterior
  have hZ := arrangement_cost Z D n p q hT H M.coherent hx' hk hs' hh hf hu (le_trans (le_of_lt ‹u<s›) hv) ‹u<s›
  apply RateLE.transfer (RateLE.mono hZ (by linarith only [div_lt_iff₀ (sub_pos.mpr ‹u<s›) |>.mp hn, sub_pos.mpr ‹u<s›]))
  filter_upwards [(hk.mono hv|>.chorus hh (hs.mono ((le_of_lt ‹u<s›).trans hv))).inject,(Kept.sole φ T x 1|>.chorus hh (hf.mono ((le_of_lt ‹u<s›).trans hv))).inject] with i hP hC
  apply le_trans (le_of_eq (congr_arg norm (?_ : _= glance Z (l i) _))) (glance_bound Z (l i) _)
  rw [glance_terms Z D n _ p _ _ q (l i) hP hC]
  let S':=spectator Z (l i); let m:= readExpr D S'; let K:= tokenWord D (Y i) q; change m ((tokenWord D (X i) p - E i)*K)=_
  rw [sub_mul,map_sub, show m (tokenWord D (X i) p*K) = observe S' (beside (X i) (Y i)) (beside p q) by unfold m K; rw [← token_beside, read_word D M.coherent S' (spectate Z (l i)).laws.toSymmetric (spectate_respects Z _) (spectate_ready Z _),totalObserve,if_pos hP] ]
  congr 1; unfold E internal Prescription.truncated; rw [Finset.sum_mul,map_sum]; refine Finset.sum_congr rfl fun j _=>?_
  rw [smul_mul_assoc,map_smul]; unfold Prescription.termRead K m; rw [← token_sole,← token_beside, read_word D M.coherent S' (spectate Z (l i)).laws.toSymmetric (spectate_respects Z _) (spectate_ready Z _),totalObserve,if_pos hC]; rfl
omit ha hs hu H hx hk hv hU hnb -- trim
lemma plus (h : Matchable Z M φ T A x s u c e) (k : Matchable Z M φ T A x s u c f) : Matchable Z M φ T A x s u c (e+f):= by
   refine ⟨fun q=>?_⟩; obtain ⟨X,h,hp⟩:= h.replaces q; obtain ⟨Y,k,hq⟩:= k.replaces q; refine ⟨X+Y,h.plus k,?_⟩; rw [show e+f-(X+Y)=e-X+(f-Y) from by abel]; exact Against.plus hp hq hT
omit hT in
lemma coeff (h : Matchable Z M φ T A x s u c e){g : W→ℂ}(hh : RateLE φ T g d) : Matchable Z M φ T A x s u (d+c) (fun i=>g i • e i):= by
   refine ⟨fun q=>?_⟩; obtain ⟨f,h,hp⟩:=h.replaces (q-d); have hu:= Against.coeff hp hh; rw [add_sub_cancel ..] at hu; refine ⟨_,h.coeff hh,Against.ident hu ?_⟩; filter_upwards with i; exact smul_sub (g i) (e i) (f i)
include ha hs hu H hx hv hnb
lemma input (h : Fine M φ T A s c e) : Matchable Z M φ T A x s u c e := by
   induction h with
   | zero => exact ⟨fun _=>⟨0,.zero, sub_zero (0:EP) ▸ Against.zero⟩⟩
   | @atom I _ X p f hk hA hf=> exact sub_add_cancel c _ ▸ (from_word hT H p ha hs hu hv hx hk hA).coeff hf
   | plus _ _ h k=> exact h.plus hT k -- dot order?
   | germ _ h hx=> exact ⟨fun q=> by obtain ⟨f,hx,h'⟩:= hx.replaces q; exact ⟨_,hx,Against.ident h' (h.sub (Eventually.of_forall fun i=>rfl))⟩⟩

lemma layer (h : Funds Z M φ T A s c e) : Matchable Z M φ T A x s u c e := by
  refine ⟨fun q=>?_⟩; obtain ⟨f,h,hp⟩:= h.enter q; obtain ⟨g,hh,hq⟩:= (input hT H ha hs hu hv hx h).replaces q
  refine ⟨g,hh,?_⟩; rw [show e-g=e-f+(f-g) from by abel]; exact Against.plus (Against.mono hp hs.le le_rfl (by rfl)) hq hT
lemma fall (h : Funds Z M φ T A s c e) : Funds Z M φ T A u c e:= ⟨h.loose, fun q=> by
  obtain ⟨f,hh,hL⟩:=(layer hT H ha hs hu hv hx h).replaces q; exact ⟨_, (hh.mono hs.le le_rfl).fine hT hx,hL⟩⟩
end Matchable
end YM.Contacts.Layers
