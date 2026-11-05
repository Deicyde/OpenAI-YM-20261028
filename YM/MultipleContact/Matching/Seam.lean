import YM.MultipleContact.Matching.Broad
import YM.MergeProof.West.News

/-! Separation with offsets lying away from every face of the centered tiling. Unlike `Ribbons.acorns` the exterior alignment need not be coarser than the tiling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Local
open YM.MergeProof YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage YM.Next.UVStress
open YM.Extraction.Around
variable {G:Gauge}(C:Family G){F:Extraction.Order}{d l D J K N m p:ℕ}
variable {n:ℕ}(q:Fin n → C.book.Token)
-- the first input is matched at origin here; the second one is also held in the same cell by the cutoff lemma.
def Locations (p:ℕ)(r:ℝ) (ℓ:Fin n→ Cover)(z:Points n) : Prop:=∀ (k:Fin n)(i:Axis), |z k i - C.S.gridPoint p (ℓ k) i| < C.S.a p/2-r -- replace
lemma d0 {p J:ℕ}: location C.S J J p (0:Cover)=0:=(Next.UVStress.location_origin ..)
private lemma seamRel (ℓ x:Cover)(K:ℕ) {r:ℝ} (hJ:J≤N){t:ℕ}(h:t ≤ N)(hR:∀ a:Axis, |C.S.gridPoint t x a - C.S.gridPoint J ℓ a| < C.S.a J/2-r) (hx:(K+2:ℝ)*C.S.a N ≤ r):
    location C.S t N p x ∈ (center C.S p hJ 0).margin ((wrap (C.S.side J p)) ℓ) K:=by
    let T:= center C.S p hJ 0; let size:= (C.S.toDepth h p).count.val
    let ys :=(location C.S t N p x); let b:ℕ:=T.side.val/2; let v:=wrap (C.S.side J p) ℓ
    have he₁:C.S.a N*T.side.val=C.S.a J:= C.S.embeds_scale (C.S.toDepth hJ p)
    have he₂:C.S.a N*size=C.S.a t:= C.S.embeds_scale (C.S.toDepth h p)
    have hf:C.S.a N*((T.side.val:ℝ)/2-r/C.S.a N)=C.S.a J/2-r:= by rw [mul_sub, ← mul_div_assoc,he₁,mul_div_cancel₀ _ (C.S.a_pos _).ne']
    let off i :ℤ:=((size:ℤ)*(x i))-((T.side.val:ℤ)*ℓ i)
    have h₃(i): |(off i:ℝ)| < (T.side.val:ℝ)/2-r/C.S.a N := (mul_lt_mul_iff_right₀ (C.S.a_pos N)).1 (by -- use field_simp? replace
       have hh:= hR i
       have hx' := C.S.a_pos N
       rw [hf,← abs_of_pos hx', ← abs_mul]; unfold off; push_cast only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,Nat.cast_ofNat]; rw [mul_sub,← mul_assoc, ← mul_assoc,he₁,he₂]; exact hh)
    have hK':r/C.S.a N ≥ (K+2:ℝ):= (le_div_iff₀ (C.S.a_pos N)).2 hx
    have hw i:= lt_of_lt_of_le (h₃ i) (sub_le_sub_left hK' ((T.side.val:ℝ)/2))
    have hb':(T.side.val:ℝ)/2-1 ≤ b ∧ (b:ℝ)≤(T.side.val:ℝ)/2:= by constructor; refine sub_le_iff_le_add.mpr ((div_le_iff₀ zero_lt_two).mpr ?_); refine le_trans ?_ (le_of_lt (by linarith : (b:ℝ)*2+1<(b+1)*2)); exact_mod_cast (show T.side.val≤b*2+1 by unfold b; omega); apply le_div_iff₀ zero_lt_two |>.2; exact_mod_cast (show b*2≤T.side.val by unfold b; omega)
    let u i :ℤ := off i+b
    have hu(i): (K:ℤ) < u i ∧ u i + (K:ℤ) < (T.side.val:ℤ) :=by
        obtain ⟨h₁,h₂⟩ := abs_lt.mp (hw i)
        suffices h:(K:ℝ) < (u i) ∧ (u i:ℝ)+K < (T.side.val:ℝ) from by exact_mod_cast h
        unfold u; push_cast; constructor <;> linarith only [hb'.1,hb'.2,h₁,h₂]
    have he (i): T.coordinated v ys i = (u i).toNat:=by
       let S:= C.S.side N p
       have hA : T.units.root v =wrap _ (T.side.val • ℓ):=by change T.units.embed (wrap _ ℓ)=_; exact T.units.embed_wrap _
       have hB : ys =wrap _ (size • x):= by unfold ys Cells.location; rw [dif_pos h,(C.S.toDepth h p).embed_wrap]
       unfold Tiling.coordinated; rw [← ZMod.val_natCast_of_lt (a:= (u i).toNat) (?_)] -- inspect names
       · apply congr_arg ZMod.val
         rw [← Int.cast_natCast,Int.toNat_of_nonneg (le_trans (by positivity) (hu i).1.le)]
         unfold Tiling.starts; rw [Pi.add_apply,hA,hB]
         change ((↑(size • x i:ℤ):Per S)-((0:Per S)-↑b+↑(T.side.val • ℓ i:ℤ))) = _
         unfold u off
         simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, nsmul_eq_mul]; ring
       have hi:=hu i; have hi':(u i).toNat < T.side.val:=(by omega); exact Nat.lt_trans hi' T.narrow
    constructor
    · intro i; change T.coordinated v ys i < T.side.val; rw [he]; have hi:=hu i; omega
    intro i; change _ ∧ T.coordinated v ys i + K + 1 ≤ T.side.val; rw [he]; have hi:=hu i; omega
-- holds uniformly for sequence of Watches (same tokens); period lateness inside each Watch. No field cutoff label assumed.
def Acorn (I:Watch C) (J:ℕ) (A:ℝ) : Prop:=∀ᶠ i : ℕ×ℕ in F.fuse, ∃ hN : J+1 ≤ i.1, ∀ f : Config G (C.side i.1 i.2) → ℂ, let T := center C.S i.2 ((Nat.le_succ J).trans hN) 0; Interior (T.chamber 0) f → ‖moment (C.beta i.1 i.2) (fun x => f x * I.plot i.1 i.2 x)‖ ≤ T.rootTest (C.beta i.1 i.2) f * A
lemma acornsS (hp:C.Makes)(h:CellHyp C F) (J:ℕ)(ℓ:Fin n→ Cover) (he: Function.Injective (Fin.cons (α:=fun _=>Cover) 0 ℓ)){r:ℝ}(hr:0<r):
    ∃A:ℝ,0≤A∧∀ (x) (t:ℕ) (hw:Extraction.Order.grid C t (Fin.cons 0 x) ∈ generic _) (hR:∀ j a, |C.S.gridPoint t (x j) a - C.S.gridPoint J (ℓ j) a| < C.S.a J/2-r), Acorn C (F:=F) {n:=n,t:=t,q:=q,x:=x,wild:=hw} J A:=by
    obtain ⟨j,⟨⟨A,hA,H⟩,hJ⟩,hj⟩ := (((YM.Next.UVStress.grows h q).and (eventually_ge_atTop (J+1))).and ((C.S.shrinks.const_mul (3:ℝ)).eventually (gt_mem_nhds (show (3*(0:ℝ))<r/2 by rw [mul_zero]; positivity)))).exists -- grows namespace
    refine ⟨A^n,pow_nonneg hA _,fun x t hw hR=>?_⟩
    let z:=Fin.cons (α:=fun _=>Cover) 0 ℓ
    have hD : ∀ᶠ i:ℕ×ℕ in F.fuse, Injective ((wrap (C.S.side J i.2)) ∘ z):=by
       rw [Extraction.Order.fused,Extraction.Order.late]; exact (F.per.cofinal.eventually (sparse C.S J z he)).mono fun _ he=> Eventually.of_forall fun _=>he
    have hQ:∀ᶠ v':ℕ×ℕ in F.fuse, (3*C.S.a j + 2*C.S.a v'.1:ℝ) ≤ r:= by
        obtain ⟨j',hj'⟩:= eventually_atTop.mp ((C.S.shrinks.const_mul 2).eventually (gt_mem_nhds (show (2*(0:ℝ))< r/2 from by rw [mul_zero]; positivity)))
        filter_upwards [large_mesh F j'] with i hi; change _ ≤ _; specialize hj' _ hi; change 3*C.S.a j < r/2 at hj; linarith
    have hH : ∀ᶠ i in F.fuse,Around.imageBudget q A j i.1 i.2 := H -- check dq
    filter_upwards [hD,hQ,hH,large_mesh F t] with i hi hQ hm hv
    let N:=i.1; let p:=i.2; let I:Watch C:={t:=t,n:=n,x:=x,q:=q,wild:=hw}
    have hn : j≤N:= hm.1; have h':J≤N:=(by omega); let T:=center C.S p h' 0; have ht':t≤ N:=hv
    let g (s:Fin (I.n+1)) : T.Cell:=wrap (C.S.side J p) (z s); let d:=3*Cells.span C.S hn p
    have hS (s:Fin n): I.among N p s ∈ T.margin (g s.succ) d := by
         apply seamRel (C:=C) (r:=r) _ _ _ h' ht' (hR s); dsimp only [d]; push_cast; change (3* ((C.S.toDepth hn p).count.val:ℝ) + 2)* C.S.a N ≤ _
         rw [add_mul,mul_assoc,mul_comm (↑_) (C.S.a N),C.S.embeds_scale]; exact hQ
    choose U hU hU' hX using fun s:Fin I.n=> Lease.alive (T:=T) hp s (I.among N p s) hm hn (inherits (by omega : J≤j) hn) (hS s) -- shadow error p'
    refine ⟨hJ.trans hn,fun f hf=>?_⟩; let D : Fin (I.n+1) → Config G (C.side N p) → ℂ := Fin.cons f U
    have hi' : ∀ (i : Fin (I.n+1)), Interior (T.chamber 0) (D i) := Fin.cases hf hU'
    have hw (x) : (∏ i : Fin (I.n+1), T.copy (g i) (D i) x)= f x * I.plot N p x := by
       have h0 : g 0=0 := by dsimp [g,z]; exact map_zero _ -- fix if simp solved
       rw [Fin.prod_univ_succ,h0,T.copy_zero]; congr 1
       exact Finset.prod_congr rfl fun j _ => congr_fun (hU j) x
    have hx:=T.planted (h.all _ _) g hi D hi'
    simp_rw [hw] at hx; apply hx.trans; rw [Fin.prod_univ_succ]; refine mul_le_mul_of_nonneg_left ?_ (T.root_nonneg (C.beta N p) f)
    refine (Finset.prod_le_prod (fun _ _=> T.root_nonneg _ _) (fun _ _=> hX _)).trans_eq (by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl)
end YM.MultipleContact.Local
