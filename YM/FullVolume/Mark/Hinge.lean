import YM.FullVolume.Mark.Sanctum
/-!
# step on ALL graph points
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
structure Gram (F:Labels.Frame G d)(Y:Hol G){n:Side}(c:Desk G n)(a:ℝ) where
   g : F.Coeff →ₗ[ℂ] Coin F Y c
   toll v: ‖g v‖ ≤ a * F.coeffSize (F.core v)
abbrev Gram.scythe {n:Side}{c:Desk G n}{a:ℝ} (T:Gram F Y c a) : F.Index→ Coin F Y c:= fun i=> T.g (Size.axis F i)
variable {S: Desk G (H.S.side (m+1) p)}{E:Desk G (H.S.side m p)}
set_option quotPrecheck false
local notation "T₀" => H.rep N p m
local notation "T₁" => H.rep N p (m+1)
local notation "U₀"=> (H.levels.params m).columns
local notation "U₁"=> (H.levels.params (m+1)).columns
local notation "k₀"=> kappa H m
local notation "k₁"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
set_option quotPrecheck false
variable (P : Tool F H N p m){W:Worth}{u ζ v t:ℝ}{D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{T:Heading F}{X:Set Wing}
variable (h:Tool.Cap P B Y W D T u ζ v X) (hw:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))) (hu:Well (H.rep N p m) E (Real.sqrt (H.levels.clock.forcedAllowance m))) (hp: roomCost H.levels W)(hk:Bank W H.levels)
namespace Gram
variable (Q:Gram F Y S ((H.levels.params (m+1)).columns))
abbrev point : F.Coeff → Coefficient F (H.S.side m p):= P.pages Q.scythe
local notation "U"=> Q.point P
include h hp hk hw
lemma prose (x:F.Coeff): let Z:= point P Q x; let g:= F.coeffSize Z.x
   Z.Format 0 Y T₀ ∧ Z.remBound 0 T₀ k₀ (U₀ *F.coeffSize (F.core Z.x)) ∧ F.coeffSize x ≤ U₁*g:=by
     intro z g; obtain ⟨hv,hQ,hx⟩:= P.stained h hw Q.scythe (fun i=> Q.toll _) x; obtain ⟨hf,hp,-⟩:= Work.G08.cone_step W H hp hk m F _ _ _ _ hx le_rfl; exact ⟨hv, rem_mono hQ hf,hp⟩
omit h hp hk hw
lemma onto : Ledger F (H.S.side m p) (Q.point P):= pencil_ledger (code _) (P.portfolio Q.scythe) (chips F)
def reads : F.Coeff→ₗ[ℂ] F.Coeff:= IsLinearMap.mk' _ (Q.onto P).x
lemma column (v:F.Coeff): (U v).x= Q.reads P v:= rfl
include h hp hk hw
lemma insertion : Function.Injective (Q.reads P):=by
   apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_); intro i hi
   have hv : (U i).x=0:=hi; apply Work.G08.size_separates
   simpa only [hv,Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero] using (Q.prose P h hw hp hk i).2.2
-- receipt. these depend `hx` through construction; adjoint reentry actually on tale.
def index := LinearEquiv.ofBijective (Q.reads P) (show Bijective (Q.reads P) from ⟨Q.insertion P h hw hp hk,LinearMap.injective_iff_surjective.mp (Q.insertion P h hw hp hk)⟩)
include hu
theorem posi (v:F.Coeff): Pay F Y E (capture (U v) P.down) (U₀*F.coeffSize (F.core (Q.index P h hw hp hk v))):= alongPay hu _ (U _) (prose P h hw hp hk Q _|>.1) (prose P h hw hp hk Q _|>.2.1)
abbrev held (x:F.Coeff): Coin F Y E:= Coin.saver F Y E _ (posi P h hw hu hp hk Q x)
lemma represented (x:F.Coeff): Coin.uses (Q.held P h hw hu hp hk x)=capture (U x) P.down:=rfl
def recorded : F.Coeff →ₗ[ℂ] Coin F Y E:= by
   apply IsLinearMap.mk' (held P h hw hu hp hk Q); exact packer P.down U (Q.onto P) _ hu (fun i=> (prose P h hw hp hk Q i).1) (fun i=> (prose P h hw hp hk Q i).2.1)
lemma fits (x:F.Coeff): ‖Q.recorded P h hw hu hp hk x‖≤ U₀*F.coeffSize (F.core (Q.index P h hw hp hk x)):= (Coin.wealths (Q.held P h hw hu hp hk x)).mpr (Q.posi P h hw hu hp hk x)
local notation "V"=> (Q.index P h hw hp hk)
def step: Gram F Y E ((H.levels.params m).columns) where
   g := Q.recorded P h hw hu hp hk ∘ₗ (Q.index P h hw hp hk).symm.toLinearMap
   toll v:= by have hh:=Q.fits P h hw hu hp hk ((V).symm v); rw [(V).apply_symm_apply] at hh; exact hh
lemma signs (v:F.Coeff): (Q.step P h hw hu hp hk).g ((V) v)=(Q.recorded P h hw hu hp hk v):=by
    change Q.recorded P h hw hu hp hk ((V).symm ((V) v))=_; rw [(V).symm_apply_apply]
end Gram
-- S.Record only.
section chord
variable {N p m:ℕ}{V:Voice F H p m}(h:Heard B H N p Y m V){S:Desk G (H.S.side m p)} (K:Keeper (H.rep N p m).p (H.rep N p m).activities)(hk:Well (H.rep N p m) S (Real.sqrt (H.levels.clock.forcedAllowance m)))
abbrev duly (x:F.Coeff):Coin F Y S:= Coin.saver F Y S _ (alongPay hk K _ (h.earns x).1 (h.earns x).2)
lemma track : IsLinearMap ℂ (duly h K hk):= packer K V.plays h.book _ hk (fun i=> (h.earns i).1) (fun i=> (h.earns i).2)
def measure : Gram F Y S ((H.levels.params m).columns) where
   g := IsLinearMap.mk' _ (track h K hk) ∘ₗ V.index.symm.toLinearMap
   toll v:=by
      have he:= (h.cone (V.index.symm v))
      rw [V.index.apply_symm_apply] at he
      exact ((Coin.wealths (duly h K hk (V.index.symm v))).mpr (alongPay hk K _ (h.earns _).1 (h.earns _).2)).trans he
lemma notations (v:F.Coeff): Coin.uses ((measure h K hk).g v)= capture (V.plays (V.index.symm v)) K:= rfl
end chord
end YM.MergeProof.Matric
