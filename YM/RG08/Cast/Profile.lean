import YM.RG08.Cast.Seat

/-! # Bind Sworn requirement to available schedule data; canonical curvature base cut-stability.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar Next.Free Rows Bid Precision Loop
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {G:Gauge}{K:KernelChoices}{s:Supply.Sheet G}

private lemma shadowCert {a:Levels G}{_P _Q:MapPrices}{_X:Horizon a}{Γ:ℕ→ℝ}{fit:∀ i,0<Γ i}
    {_Y:Horizon (Flat.shadow a Γ fit)} :True:=trivial

lemma assured (G:Gauge)(K:KernelChoices)(s:Supply.Sheet G)(hs:s.kernel=K):
    ∃ E:ℕ→ℕ, ∀ (a:Levels G), a.clock.kernel=s.kernel→a.clock.stage=s.profile→(∀ i,E (a.clock.J (i+1)) ≤ (a.S.block i).val)→∀ (T:Horizon a){P:MapPrices},T.Suffices P →∀ i N n,i≤N→Sworn (T.H N i) n G:=by
 obtain ⟨q,r,γ,m,HC,HK⟩:=retained_support (G:=G) K
 let s':={s with profile:=fun i=>rearrange (s.profile i) (γ i) (HC.fit i)}
 obtain ⟨X,H⟩:= HK s' hs
 refine ⟨m,fun a ha hA he T ph hP i N n hi=>?_⟩
 let b:=Flat.shadow a γ HC.fit
 have hC : Credit b γ m := ⟨fun _=>le_rfl, he⟩
 have hz:b.clock.stage=s'.profile:=by funext i; unfold b Flat.shadow Flat.adjust s'; simp only [hA]
 obtain ⟨_,Y,-,-,-,hY,-,hy'⟩:=H b ha hz hC
 have hQ:Flat.output (T.H N i)=Flat.output (Y.H N i):=same_shadow a γ HC.fit hP hY N i hi
 have hr n : Flat.quadratic (T.H N i) n=Flat.quadratic (Y.H N i) n:=by
    have hM (a:Levels G)(T:Horizon a){P:MapPrices}(hP:T.Suffices P): Matches (Flat.output (T.H N i)) (Flat.quadratic (T.H N i) n):=by
       exact ((Flat.output_cost (σ:=min 1 (P.α (a.clock.J i))) (fun j k=> ((hP.rows N i hi).2.1 j k).mono (min_le_right ..) le_rfl) (Ω_pos hP i) (le_min zero_le_one (P.alpha_pos _).le) (min_le_left ..))).2 _
    ext x y; obtain ⟨j,k⟩:=x
    have hw:=hM a T hP ((lift j,k):Market _) y;have hz:=hM b Y hY ((lift j,k):Market _) y
    dsimp only at *;rw [wrap_lift,hQ] at hw;rw [wrap_lift] at hz; exact hw.symm.trans hz
 have hh :=hy' N i n hi
 unfold Sworn gaugeFiscal;intro x f g;simp_rw [hr n];exact hh x f g
