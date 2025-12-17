import { fireEvent, render, screen } from '@testing-library/react';
import React from 'react';

import Modal from './index';

describe('Modal', () => {
  beforeEach(() => {
    document.body.style.overflow = '';
  });

  it('should not render when isOpen is false', () => {
    render(
      <Modal isOpen={false} onClose={jest.fn()} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    expect(screen.queryByText('Test Modal')).not.toBeInTheDocument();
  });

  it('should render when isOpen is true', () => {
    render(
      <Modal isOpen={true} onClose={jest.fn()} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    expect(screen.getByText('Test Modal')).toBeInTheDocument();
    expect(screen.getByText('Modal Content')).toBeInTheDocument();
  });

  it('should call onClose when close button is clicked', () => {
    const handleClose = jest.fn();
    render(
      <Modal isOpen={true} onClose={handleClose} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    const closeButton = screen.getByTitle('back');
    fireEvent.click(closeButton);

    expect(handleClose).toHaveBeenCalledTimes(1);
  });

  it('should call onClose when backdrop is clicked', () => {
    const handleClose = jest.fn();
    render(
      <Modal isOpen={true} onClose={handleClose} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    const backdrop = screen
      .getByText('Test Modal')
      .closest('.fixed')
      ?.querySelector('.absolute');
    if (backdrop) {
      fireEvent.click(backdrop);
      expect(handleClose).toHaveBeenCalledTimes(1);
    }
  });

  it('should call onClose when Escape key is pressed', () => {
    const handleClose = jest.fn();
    render(
      <Modal isOpen={true} onClose={handleClose} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    fireEvent.keyDown(document, { key: 'Escape', code: 'Escape' });

    expect(handleClose).toHaveBeenCalledTimes(1);
  });

  it('should lock body scroll when open', () => {
    render(
      <Modal isOpen={true} onClose={jest.fn()} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    expect(document.body.style.overflow).toBe('hidden');
  });

  it('should restore body scroll when closed', () => {
    const { rerender } = render(
      <Modal isOpen={true} onClose={jest.fn()} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    expect(document.body.style.overflow).toBe('hidden');

    rerender(
      <Modal isOpen={false} onClose={jest.fn()} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    expect(document.body.style.overflow).toBe('unset');
  });

  it('should apply default size classes', () => {
    render(
      <Modal isOpen={true} onClose={jest.fn()} title='Test Modal'>
        <div>Modal Content</div>
      </Modal>
    );

    const modal = screen.getByText('Test Modal').closest('.absolute');
    expect(modal).toHaveClass('max-w-4xl');
  });

  it('should apply large size classes', () => {
    render(
      <Modal isOpen={true} onClose={jest.fn()} title='Test Modal' size='large'>
        <div>Modal Content</div>
      </Modal>
    );

    const modal = screen.getByText('Test Modal').closest('.absolute');
    expect(modal).toHaveClass('max-w-6xl');
  });

  it('should apply full size classes', () => {
    render(
      <Modal isOpen={true} onClose={jest.fn()} title='Test Modal' size='full'>
        <div>Modal Content</div>
      </Modal>
    );

    const modal = screen.getByText('Test Modal').closest('.absolute');
    expect(modal).toHaveClass('max-w-[95vw]');
  });
});
